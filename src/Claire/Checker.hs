{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
module Claire.Checker where

import Control.Monad.State.Strict
import Control.Monad.Catch
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Exception.Base (ErrorCall)
import qualified Data.Map as M
import Data.Foldable
import Language.Haskell.Interpreter hiding (get, infer)
import System.FilePath

import Claire.Syntax
import Claire.Parser
import Claire.Env
import Claire.Typecheck


newGoal :: Formula -> [Judgement]
newGoal fml = [Judgement [] (return fml)]

judge :: Env -> [Rule] -> [Judgement] -> Either (Rule, [Judgement]) [Judgement]
judge thms rs js = foldl (\m r -> m >>= go r) (Right js) rs where
  go I (Judgement assms props : js) | length assms == 1 && assms == props = Right js
  go (Cut fml) (Judgement assms props : js) = Right $ Judgement assms (fml:props) : Judgement (fml:assms) props : js
  go AndL1 (Judgement ((fa :/\: fb):assms) props : js) = Right $ Judgement (fa:assms) props : js
  go AndL2 (Judgement ((fa :/\: fb):assms) props : js) = Right $ Judgement (fb:assms) props : js
  go AndR (Judgement assms ((fa :/\: fb):props) : js) = Right $ Judgement assms (fa:props) : Judgement assms (fb:props) : js
  go OrL (Judgement ((fa :\/: fb):assms) props : js) = Right $ Judgement (fa:assms) props : Judgement (fb:assms) props : js
  go OrR1 (Judgement assms ((fa :\/: fb):props) : js) = Right $ Judgement assms (fa:props) : js
  go OrR2 (Judgement assms ((fa :\/: fb):props) : js) = Right $ Judgement assms (fb:props) : js
  go ImpL (Judgement ((fa :==>: fb):assms) props : js) = Right $ Judgement assms (fa:props) : Judgement (fb:assms) props : js
  go ImpR (Judgement assms ((fa :==>: fb):props) : js) = Right $ Judgement (fa:assms) (fb:props) : js
  go BottomL (Judgement (Bottom:assms) props : js) = Right js
  go TopR (Judgement assms (Top:props) : js) = Right js
  go (ForallL t) (Judgement (Forall x fml:assms) props : js) = Right $ Judgement (substTerm x t fml:assms) props : js
  go (ForallR y) (Judgement assms (Forall x fml:props) : js) = Right $ Judgement assms (substTerm x (Var y) fml:props) : js
  go (ExistL y) (Judgement (Exist x fml:assms) props : js) = Right $ Judgement (substTerm x (Var y) fml:assms) props : js
  go (ExistR t) (Judgement assms (Exist x fml:props) : js) = Right $ Judgement assms (substTerm x t fml:props) : js

  go WL (Judgement (_:assms) props : js) = Right $ Judgement assms props : js
  go WR (Judgement assms (_:props) : js) = Right $ Judgement assms props : js
  go CL (Judgement (fml:assms) props : js) = Right $ Judgement (fml:fml:assms) props : js
  go CR (Judgement assms (fml:props) : js) = Right $ Judgement assms (fml:fml:props) : js
  go (PL k) (Judgement assms props : js) | k < length assms = Right $ Judgement (assms !! k : deleteAt k assms) props : js
  go (PR k) (Judgement assms props : js) | k < length props = Right $ Judgement assms (props !! k : deleteAt k props) : js

  go r js = Left (r,js)

  deleteAt k xs = take k xs ++ drop (k+1) xs

--

data ComSuspender y
  = ComAwait (Command -> y)
  | CommandError Ident SomeException y
  deriving (Functor)

instance Show (ComSuspender y) where
  show (ComAwait _) = "ComAwait"
  show (CommandError com err _) = com ++ ": " ++ show err

data CommandError
  = NoSuchTheorem Ident
  | CannotApply Rule [Judgement]
  | CannotInstantiate SomeException
  | NewCommandError Argument SomeException
  | NoSuchCommand
  deriving (Show)

instance Exception CommandError

comrunner :: (Monad m, MonadIO m) => Env -> [Command] -> StateT [Judgement] m ()
comrunner env = go (commandM env) where
  go cr cs = do
    r <- resume cr
    case r of
      Left (ComAwait k) -> case cs of
                             [] -> return ()
                             (c:cs') -> go (k c) cs'
      Left err -> liftIO $ throwM $ (error $ "comrunner: " ++ show err ++ "\n" ++ show env :: ErrorCall)
      Right () -> return ()

commandM :: (Monad m, MonadIO m) => Env -> Coroutine ComSuspender (StateT [Judgement] m) ()
commandM env = do
  com <- suspend $ ComAwait return
  let insts fml pairs = foldlM (\f (idt,pred) -> substPred ('?':idt) pred f) fml pairs
  
  case com of
    Apply rs -> do
      js <- lift get
      case judge env rs js of
        Left (r,js') -> do
          suspend $ CommandError "apply" (toException $ CannotApply r js') (return ())
          commandM env
        Right js' -> lift $ put js'
    NoApply r -> do
      js <- lift get
      case judge env [r] js of
        Left (r,js') -> do
          suspend $ CommandError "noapply" (toException $ CannotApply r js') (return ())
          commandM env
        Right js' -> do
          liftIO $ putStrLn $ "= NoApply " ++ show r ++ " result"
          liftIO $ mapM_ print js'
          liftIO $ putStrLn $ "=\n"
    Use idx pairs | idx `M.member` thms env -> do
      let fml = thms env M.! idx
      case insts fml pairs of
        Right r -> lift $ modify $ \(Judgement assms props : js) -> Judgement (r:assms) props : js
        Left err -> suspend $ CommandError "inst" (toException $ CannotInstantiate err) (return ())
    Use idx pairs -> suspend $ CommandError "use" (toException $ NoSuchTheorem idx) (return ())
    Inst idt pred -> do
      js <- lift get
      case js of
        [] -> suspend $ CommandError "inst" (toException (error "empty judgement" :: ErrorCall)) (return ())
        (Judgement (assm:assms) props : js') -> do
          case substPred ('?':idt) pred assm of
            Right r -> lift $ put $ Judgement (r:assms) props : js'
            Left err -> suspend $ CommandError "inst" (toException $ CannotInstantiate err) (return ())
    NewCommand com args | M.member com (newcommands env) -> do
      js <- lift get
      r <- liftIO $ (Right <$> (newcommands env M.! com) env args js) `catch` \(e :: SomeException) -> throwM e
      case r of
        Right js' -> lift $ put js'
        Left err -> suspend $ CommandError com err (return ())
    NewCommand com args -> suspend $ CommandError com (toException NoSuchCommand) (return ())

  js <- lift get
  unless (null js) $ commandM env

data DeclSuspender m y
  = DeclAwait (Decl -> y)
  | ProofNotFinished [Judgement] (Command -> y)
  | IllegalPredicateDeclaration Formula y
  | IllegalTermDeclaration Term y
  | HsFileLoadError InterpreterError y
  | TypeError Formula SomeException y
  | ComError (ComSuspender (Coroutine ComSuspender (StateT [Judgement] m) ())) y
  deriving (Functor)

instance Show (DeclSuspender m y) where
  show (DeclAwait _) = "DeclAwait"
  show (ProofNotFinished js _) = "ProofNotFinished: " ++ show js
  show (IllegalPredicateDeclaration fml _) = "IllegalPredicateDeclaration: " ++ show fml
  show (IllegalTermDeclaration t _) = "IllegalTermDeclaration: " ++ show t
  show (HsFileLoadError err _) = "HsFileLoadError: " ++ show err
  show (ComError e _) = "ComError: " ++ show e
  show (TypeError fml err _) = "TypeError(" ++ show fml ++ "): " ++ show err

toplevelM :: (Monad m, MonadIO m) => Coroutine (DeclSuspender m) (StateT Env m) ()
toplevelM = forever $ do
  let typecheck fml u k = do {
    env <- lift get;
    utyp <- liftIO $ try $ infer env fml;
    case utyp of
      Left err -> suspend $ TypeError fml err (return ())
      Right typ | u == typ -> k
      Right typ -> suspend $ TypeError fml (toException $ UnificationFailed u typ) (return ())
  }
 
  decl <- suspend (DeclAwait return)
  case decl of
    AxiomD idx fml -> typecheck fml Prop $ do
      lift $ modify $ insertThm idx fml
    ThmD idx fml (Proof coms) -> typecheck fml Prop $ do
      lift $ modify $ \env -> env { proof = [] }
      runThmD idx fml coms
    ImportD path -> do
      env <- lift get
      env' <- liftIO $ claire env . (\(Laire ds) -> ds) . pLaire =<< readFile path
      lift $ put $ env'
    ConstD p typ -> do
      lift $ modify $ \env -> env { types = M.insert p typ (types env) }
    PrintProof -> do
      env <- lift get
      liftIO $ putStrLn $ print_proof env
    HsFile file -> do
      r <- liftIO $ runInterpreter $ do
        loadModules [file]
        setTopLevelModules [takeBaseName file]
        interpret "export" (as :: [(String, Env -> Argument -> [Judgement] -> IO [Judgement])])
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

          case result of
            Right () -> return ()
            Left (ComAwait cont) -> do
              case coms of
                [] -> do
                  com' <- suspend $ ProofNotFinished js' return
                  go (suspend $ ComAwait cont) js' [com']
                (c:cs) -> do
                  go (cont c) js' cs
            Left (z@(CommandError _ _ cont)) -> suspend (ComError z (return ())) >> go cont js coms

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

