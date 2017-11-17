{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
module Claire.Machinery where

import Control.Monad.State.Strict
import Control.Monad.Catch
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import qualified Data.Sequence as S
import qualified Data.Map as M
import Language.Haskell.Interpreter hiding (get)
import System.FilePath
import Claire.Laire
import Claire.Checker


data ComSuspender y
  = ComAwait (Command -> y)
  | CannotApply Rule [Judgement] y
  | CannotInstantiate SomeException y
  | CommandError String String y
  deriving (Functor)

instance Show (ComSuspender y) where
  show (ComAwait _) = "ComAwait"
  show (CannotApply r js _) = show r ++ " cannot apply to " ++ show js
  show (CannotInstantiate err _) = show err
  show (CommandError com err _) = "CommandError(" ++ com ++ "): " ++ err

commandM :: (Monad m, MonadIO m) => Env -> Coroutine ComSuspender (StateT [Judgement] m) ()
commandM env = do
  com <- suspend $ ComAwait return
  case com of
    Apply rs -> do
      js <- lift get
      case judge env rs js of
        Left (r,js') -> do
          suspend $ CannotApply r js' (return ())
          commandM env
        Right js' -> lift $ put js'
    NoApply r -> do
      js <- lift get
      case judge env [r] js of
        Left (r,js') -> do
          suspend $ CannotApply r js' (return ())
          commandM env
        Right js' -> do
          liftIO $ putStrLn $ "= NoApply " ++ show r ++ " result"
          liftIO $ mapM_ print js'
          liftIO $ putStrLn $ "=\n"
    Use idx | idx `M.member` thms env -> do
      let fml = thms env M.! idx
      lift $ modify $ \(Judgement assms props : js) -> Judgement (assms S.:|> fml) props : js
    Use idx -> suspend $ CommandError (show $ Use idx) "No such theorem" (return ())
    Inst idt pred -> do
      js <- lift get
      case js of
        [] -> suspend $ CannotInstantiate (error "empty judgement") (return ())
        (Judgement (assms S.:|> assm) props : js') -> do
          case substPred ('?':idt) pred assm of
            Right r -> lift $ put $ Judgement (assms S.:|> r) props : js'
            Left err -> suspend $ CannotInstantiate err (return ())
    NewCommand com | M.member com (newcommands env) -> do
      js <- lift get
      case (newcommands env M.! com) env js of
        Left err -> suspend $ CommandError com err (return ())
        Right js' -> lift $ put js'
    NewCommand com -> suspend $ CommandError com "No such command" (return ())

  js <- lift get
  unless (null js) $ commandM env

data DeclSuspender m y
  = DeclAwait (Decl -> y)
  | ProofNotFinished [Judgement] (Command -> y)
  | IllegalPredicateDeclaration Formula y
  | IllegalTermDeclaration Term y
  | HsFileLoadError InterpreterError y
  | ComError (ComSuspender (Coroutine ComSuspender (StateT [Judgement] m) ())) y
  deriving (Functor)

instance Show (DeclSuspender m y) where
  show (DeclAwait _) = "DeclAwait"
  show (ProofNotFinished js _) = "ProofNotFinished: " ++ show js
  show (IllegalPredicateDeclaration fml _) = "IllegalPredicateDeclaration: " ++ show fml
  show (IllegalTermDeclaration t _) = "IllegalTermDeclaration: " ++ show t
  show (HsFileLoadError err _) = "HsFileLoadError: " ++ show err
  show (ComError e _) = "ComError: " ++ show e

toplevelM :: (Monad m, MonadIO m) => Coroutine (DeclSuspender m) (StateT Env m) ()
toplevelM = forever $ do
  let isVar (Var _) = True
      isVar _ = False
  decl <- suspend (DeclAwait return)
  case decl of
    AxiomD idx fml -> do
      lift $ modify $ insertThm idx fml
    ThmD idx fml (Proof coms) -> do
      lift $ modify $ \env -> env { proof = [] }
      runThmD idx fml coms
    ImportD path -> do
      env <- lift get
      env' <- liftIO $ claire env . (\(Laire ds) -> ds) . pLaire =<< readFile path
      lift $ put $ env'
    PredD fml -> do
      case fml of
        Pred p ts | all isVar ts -> lift $ modify $ \env -> env { preds = M.insert p (length ts) (preds env) }
        z -> suspend $ IllegalPredicateDeclaration z (return ())
    PrintProof -> do
      env <- lift get
      liftIO $ putStrLn $ print_proof env
    TermD trm -> case trm of
      Var v -> lift $ modify $ \env -> env { terms = M.insert v 0 (terms env) }
      Func f ts | all isVar ts -> lift $ modify $ \env -> env { terms = M.insert f (length ts) (terms env) }
      z -> suspend $ IllegalTermDeclaration z (return ())
    HsFile file -> do
      r <- liftIO $ runInterpreter $ do
        loadModules [file]
        setTopLevelModules [takeBaseName file]
        interpret "export" (as :: [(String, Env -> [Judgement] -> Either String [Judgement])])
      case r of
        Left err -> suspend $ HsFileLoadError err (return ())
        Right mp -> lift $ modify $ \env -> env { newcommands = M.union (M.fromList mp) (newcommands env) }

  where
    runThmD :: (Monad m, MonadIO m) => ThmIndex -> Formula -> [Command] -> Coroutine (DeclSuspender m) (StateT Env m) ()
    runThmD idx fml coms = do
      lift $ modify $ \env -> env { proof = [] }
      env <- lift get
      go (commandM env) (newGoal fml) coms
      lift $ modify $ insertThm idx fml

      where
        go :: Monad m => Coroutine ComSuspender (StateT [Judgement] m) () -> [Judgement] -> [Command] -> Coroutine (DeclSuspender m) (StateT Env m) ()
        go machine js coms = do
          env <- lift get
          (result,js') <- lift $ lift $ runStateT (resume machine) js

          let err_handle = \z cont -> suspend (ComError z (return ())) >> go cont js coms
          case result of
            Right () -> return ()
            Left (ComAwait cont) -> do
              case coms of
                [] -> do
                  com' <- suspend $ ProofNotFinished js' return
                  go (suspend $ ComAwait cont) js' [com']
                (c:cs) -> do
                  go (cont c) js' cs
            Left (z@(CannotApply _ _ cont)) -> err_handle z cont
            Left (z@(CannotInstantiate _ cont)) -> err_handle z cont
            Left (z@(CommandError _ _ cont)) -> err_handle z cont

claire :: Env -> [Decl] -> IO Env
claire = go toplevelM where
  go :: Coroutine (DeclSuspender IO) (StateT Env IO) () -> Env -> [Decl] -> IO Env
  go machine env decls = do
    (result,env') <- flip runStateT env (resume machine)
    case result of
      Left (DeclAwait cont) -> case decls of
        [] -> return env'
        (d:ds) -> go (cont d) env' ds
      Left z -> do
        print z
        return env'

feeds :: Monad m => [i] -> Coroutine (Await i) m a -> m (Either (Coroutine (Await i) m a , [i]) a)
feeds = go where
  go [] m = resume m >>= either (\c -> return $ Left (suspend c, [])) (return . Right)
  go (c:cs) m = resume m >>= either (\(Await k) -> go cs (k c)) (return . Right)

