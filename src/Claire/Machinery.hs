module Claire.Machinery where

import Control.Monad.State.Strict
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Catch
import Data.Typeable
import qualified Data.Sequence as S
import qualified Data.Map as M
import Claire.Laire
import Claire.Checker

data CommandException = CannotApply Rule [Judgement] deriving Show

instance Exception CommandException

commandM :: (Monad m, MonadThrow m) => Env -> Coroutine (Await Command) (StateT [Judgement] m) ()
commandM env = do
  com <- await
  case com of
    Apply rs -> lift $ do
      js <- get
      case judge env rs js of
        Left (r,js') -> lift $ throwM $ CannotApply r js'
        Right js' -> put js'
    Use idx -> lift $ modify $ \(Judgement assms props : js) -> Judgement (assms S.:|> getEnv env M.! idx) props : js

  js <- lift get
  unless (null js) $ commandM env

data DeclException m
  = ProofNotFinished (Coroutine (Await Command) (StateT [Judgement] m) ()) (StateT Env m ()) [Command] [Judgement]

instance Show (DeclException m) where
  show (ProofNotFinished _ _ cs js') = "ProofNotFinished: " ++ show cs ++ " " ++ show js'

instance Typeable m => Exception (DeclException m)

toplevelM :: (Monad m, MonadThrow m, Typeable m) => Coroutine (Await Decl) (StateT Env m) ()
toplevelM = forever $ do
  decl <- await
  case decl of
    AxiomD idx fml -> do
      lift $ modify $ insertThm idx fml
    ThmD idx fml (Proof coms) -> do
      env <- lift get
      (result, js') <- lift $ lift $ runStateT (feeds coms (commandM env)) [Judgement S.empty (S.singleton fml)]
      let fin = modify $ insertThm idx fml
      case result of
        Right () -> lift fin
        Left (k,coms) -> lift $ lift $ throwM $ ProofNotFinished k fin coms js'

feeds :: Monad m => [i] -> Coroutine (Await i) m a -> m (Either (Coroutine (Await i) m a , [i]) a)
feeds = go where
  go [] m = resume m >>= either (\c -> return $ Left (suspend c, [])) (return . Right)
  go (c:cs) m = resume m >>= either (\(Await k) -> go cs (k c)) (return . Right)

