{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
module Claire.Machinery where

import Control.Monad.State.Strict
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import qualified Data.Sequence as S
import qualified Data.Map as M
import Claire.Laire
import Claire.Checker


data ComSuspender y
  = ComAwait (Command -> y)
  | CannotApply Rule [Judgement] y
  deriving (Functor)

commandM :: (Monad m) => Env -> Coroutine ComSuspender (StateT [Judgement] m) ()
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
    Use idx -> lift $ modify $ \(Judgement assms props : js) -> Judgement (assms S.:|> getEnv env M.! idx) props : js

  js <- lift get
  unless (null js) $ commandM env

data DeclSuspender m y
  = DeclAwait (Decl -> y)
  | ProofNotFinished [Judgement] (Command -> y)
  | ComError (ComSuspender (Coroutine ComSuspender (StateT [Judgement] m) ())) y
  deriving (Functor)

toplevelM :: Monad m => Coroutine (DeclSuspender m) (StateT Env m) ()
toplevelM = forever $ do
  decl <- suspend (DeclAwait return)
  case decl of
    AxiomD idx fml -> do
      lift $ modify $ insertThm idx fml
    ThmD idx fml (Proof coms) -> runThmD idx fml coms
  where
    runThmD :: Monad m => ThmIndex -> Formula -> [Command] -> Coroutine (DeclSuspender m) (StateT Env m) ()
    runThmD idx fml coms = do
      env <- lift get
      go (commandM env) [Judgement S.empty (S.singleton fml)] coms
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
            Left (z@(CannotApply _ _ cont)) -> do
              suspend $ ComError z (return ())
              go cont js coms

feeds :: Monad m => [i] -> Coroutine (Await i) m a -> m (Either (Coroutine (Await i) m a , [i]) a)
feeds = go where
  go [] m = resume m >>= either (\c -> return $ Left (suspend c, [])) (return . Right)
  go (c:cs) m = resume m >>= either (\(Await k) -> go cs (k c)) (return . Right)

