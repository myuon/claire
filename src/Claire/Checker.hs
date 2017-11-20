{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
module Claire.Checker where

import Control.Monad.State.Strict
import Control.Monad.Catch
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import qualified Data.Sequence as S
import qualified Data.Map as M
import Language.Haskell.Interpreter hiding (get, infer)
import System.FilePath

import Claire.Syntax
import Claire.Parser
import Claire.Env


newGoal :: Formula -> [Judgement]
newGoal fml = [Judgement S.empty (S.singleton fml)]

judge :: Env -> [Rule] -> [Judgement] -> Either (Rule, [Judgement]) [Judgement]
judge thms rs js = foldl (\m r -> m >>= go r) (Right js) rs where
  go I (Judgement assms props : js) | S.length assms == 1 && assms == props = Right js
  go (Cut fml) (Judgement assms props : js) = Right $ Judgement assms (fml S.:<| props) : Judgement (assms S.:|> fml) props : js
  go AndL1 (Judgement (assms S.:|> (fa :/\: fb)) props : js) = Right $ Judgement (assms S.:|> fa) props : js
  go AndL2 (Judgement (assms S.:|> (fa :/\: fb)) props : js) = Right $ Judgement (assms S.:|> fb) props : js
  go AndR (Judgement assms ((fa :/\: fb) S.:<| props) : js) = Right $ Judgement assms (fa S.:<| props) : Judgement assms (fb S.:<| props) : js
  go OrL (Judgement (assms S.:|> (fa :\/: fb)) props : js) = Right $ Judgement (assms S.:|> fa) props : Judgement (assms S.:|> fb) props : js
  go OrR1 (Judgement assms ((fa :\/: fb) S.:<| props) : js) = Right $ Judgement assms (fa S.:<| props) : js
  go OrR2 (Judgement assms ((fa :\/: fb) S.:<| props) : js) = Right $ Judgement assms (fb S.:<| props) : js
  go ImpL (Judgement (assms S.:|> (fa :==>: fb)) props : js) = Right $ Judgement assms (fa S.:<| props) : Judgement (assms S.:|> fb) props : js
  go ImpR (Judgement assms ((fa :==>: fb) S.:<| props) : js) = Right $ Judgement (assms S.:|> fa) (fb S.:<| props) : js
  go BottomL (Judgement (assms S.:|> Bottom) props : js) = Right js
  go TopR (Judgement assms (Top S.:<| props) : js) = Right js
  go (ForallL t) (Judgement (assms S.:|> Forall x fml) props : js) = Right $ Judgement (assms S.:|> substTerm x t fml) props : js
  go (ForallR y) (Judgement assms (Forall x fml S.:<| props) : js) = Right $ Judgement assms (substTerm x (Var y) fml S.:<| props) : js
  go (ExistL y) (Judgement (assms S.:|> Exist x fml) props : js) = Right $ Judgement (assms S.:|> substTerm x (Var y) fml) props : js
  go (ExistR t) (Judgement assms (Exist x fml S.:<| props) : js) = Right $ Judgement assms (substTerm x t fml S.:<| props) : js

  go WL (Judgement (assms S.:|> _) props : js) = Right $ Judgement assms props : js
  go WR (Judgement assms (_ S.:<| props) : js) = Right $ Judgement assms props : js
  go CL (Judgement (assms S.:|> fml) props : js) = Right $ Judgement (assms S.:|> fml S.:|> fml) props : js
  go CR (Judgement assms (fml S.:<| props) : js) = Right $ Judgement assms (fml S.:<| fml S.:<| props) : js
  go (PL k) (Judgement assms props : js) | k < S.length assms = Right $ Judgement (S.deleteAt k assms S.:|> S.index assms k) props : js
  go (PR k) (Judgement assms props : js) | k < S.length props = Right $ Judgement assms (S.index props k S.:<| S.deleteAt k props) : js

  go r js = Left (r,js)


data TypeInferenceError
  = FormulaTypeMismatch Formula Type Type
  | TermTypeMismatch Term Type Type
  | NotFound Ident
  deriving (Show)

instance Exception TypeInferenceError

inferT :: Env -> Term -> Either TypeInferenceError Type
inferT env = go where
  go (Var v) | v `M.member` terms env = do
    return $ terms env M.! v
  go (Var v) = Left $ NotFound v
  go (Func v ts) | v `M.member` terms env = do
    let vty = terms env M.! v
    funtype env vty ts
  go (Func v ts) = Left $ NotFound v

expect k t1 t2
  | t1 == t2 = return t1
  | otherwise = Left $ k t1 t2

funtype env ty [] = return ty
funtype env (ArrT ty1 ty2) (t:ts) = do
  expect (TermTypeMismatch t) ty1 =<< inferT env t
  funtype env ty2 ts

infer :: Env -> Formula -> Either TypeInferenceError Type
infer env = go where
  go (Pred p ts) | p `M.member` preds env = do
    typ <- funtype env (preds env M.! p) ts
    expect (FormulaTypeMismatch (Pred p ts)) Prop typ
  go (Pred p ts) = Left $ NotFound p
  go Top = return Prop
  go Bottom = return Prop
  go (fml1 :/\: fml2) = do
    t1 <- go fml1
    expect (FormulaTypeMismatch fml1) Prop t1
    t2 <- go fml2
    expect (FormulaTypeMismatch fml2) Prop t2
  go (fml1 :\/: fml2) = do
    t1 <- go fml1
    expect (FormulaTypeMismatch fml1) Prop t1
    t2 <- go fml2
    expect (FormulaTypeMismatch fml2) Prop t2
  go (fml1 :==>: fml2) = do
    t1 <- go fml1
    expect (FormulaTypeMismatch fml1) Prop t1
    t2 <- go fml2
    expect (FormulaTypeMismatch fml2) Prop t2
  go (Forall v fml) = do
    t <- go fml
    expect (FormulaTypeMismatch fml) Prop t
  go (Exist v fml) = do
    t <- go fml
    expect (FormulaTypeMismatch fml) Prop t

--

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
  | TypeError TypeInferenceError y
  | ComError (ComSuspender (Coroutine ComSuspender (StateT [Judgement] m) ())) y
  deriving (Functor)

instance Show (DeclSuspender m y) where
  show (DeclAwait _) = "DeclAwait"
  show (ProofNotFinished js _) = "ProofNotFinished: " ++ show js
  show (IllegalPredicateDeclaration fml _) = "IllegalPredicateDeclaration: " ++ show fml
  show (IllegalTermDeclaration t _) = "IllegalTermDeclaration: " ++ show t
  show (HsFileLoadError err _) = "HsFileLoadError: " ++ show err
  show (ComError e _) = "ComError: " ++ show e
  show (TypeError err _) = show err

toplevelM :: (Monad m, MonadIO m) => Coroutine (DeclSuspender m) (StateT Env m) ()
toplevelM = forever $ do
  let isVar (Var _) = True
      isVar _ = False
  let typecheck fml u k = do {
    env <- lift get;
    case infer env fml of
      Left err -> suspend $ TypeError err (return ())
      Right typ | u == typ -> k
      Right typ -> suspend $ TypeError (FormulaTypeMismatch fml u typ) (return ())
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
    PredD fml typ -> do
      case fml of
        Pred p ts | all isVar ts -> lift $ modify $ \env -> env { preds = M.insert p typ (preds env) }
        z -> suspend $ IllegalPredicateDeclaration z (return ())
    PrintProof -> do
      env <- lift get
      liftIO $ putStrLn $ print_proof env
    TermD trm typ -> case trm of
      Var v -> lift $ modify $ \env -> env { terms = M.insert v typ (terms env) }
--      Func f ts | all isVar ts -> lift $ modify $ \env -> env { terms = M.insert f (length ts) (terms env) }
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

