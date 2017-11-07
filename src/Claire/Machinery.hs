module Claire.Machinery where

import Control.Monad.State
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import qualified Data.Sequence as S
import qualified Data.Map as M
import Claire.Laire
import Claire.Checker

commandM :: Monad m => Env -> Coroutine (Await Command) (StateT [Judgement] m) ()
commandM env = do
  com <- await
  case com of
    Apply rs -> lift $ do
      js <- get
      case judge env rs js of
        Left z -> error $ show z
        Right js' -> put js'
    Use idx -> lift $ modify $ \(Judgement assms props : js) -> Judgement (assms S.:|> getEnv env M.! idx) props : js

  js <- lift get
  unless (null js) $ commandM env

thmM :: Monad m => ThmIndex -> Formula -> Coroutine (Await Decl) (StateT Env m) ()
thmM idx fml = do
  decl <- await
  case decl of
    PrfD (Proof coms) -> do
      env <- lift get
      result <- evalStateT (feeds coms (commandM env)) [Judgement S.empty (S.singleton fml)]
      case result of
        Right () -> lift $ modify $ insertThm idx fml
        Left (k,coms) -> error "failed to finish proof..."
    z -> error $ "unexpected decl:" ++ show z

toplevelM :: Monad m => Coroutine (Await Decl) (StateT Env m) ()
toplevelM = forever $ do
  decl <- await
  case decl of
    AxiomD idx fml -> do
      lift $ modify $ insertThm idx fml
    ThmD idx fml -> do
      thmM idx fml
    z -> error $ "unexpected decl:" ++ show z

feeds :: Monad m => [i] -> Coroutine (Await i) m a -> m (Either (Coroutine (Await i) m a , [i]) a)
feeds = go where
  go [] m = resume m >>= either (\c -> return $ Left (suspend c, [])) (return . Right)
  go (c:cs) m = resume m >>= either (\(Await k) -> go cs (k c)) (return . Right)

