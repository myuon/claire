module Main where

import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.State
import Control.Monad.Catch
import Control.Monad.Except
import qualified Data.Map as M
import System.IO
import System.Environment (getArgs)
import Claire

main :: IO ()
main = do
  xs <- getArgs
  case (xs /= []) of
    True -> do
      p <- readFile (head xs)
      env <- claire defEnv . pLaire <$> readFile (head xs)
      seq env $ mapM_ putStrLn $
        [ "==========="
        , "=== QED ==="
        , "==========="
        , ""
        ]
      mapM_ print $ M.assocs $ getEnv ((\(Right r) -> r) env)
    False -> do
      mapM_ putStrLn $
        [ "========================="
        , "=== Welcome to Claire ==="
        , "========================="
        , ""
        ]
      clairepl defEnv

clairepl :: Env -> IO ()
clairepl env = runrepl env toplevelM

type Repl = StateT Env (ExceptT (DeclException IO) IO)

runrepl :: Env -> Coroutine (Await Decl) Repl () -> IO ()
runrepl env k = do
  Right (result,env') <- runExceptT $ do
    (runStateT (resume k) env) `catch` \(ProofNotFinished k fin coms js) -> lift $ go k fin js env
  putStrLn $ "env: " ++ show env'
  
  case result of
    Right () -> return ()
    Left (Await k) -> do
      putStr "decl>" >> hFlush stdout
      t <- pDecl <$> getLine

      runrepl env' (k t)

  where
    go k fin js env = do
      putStr "command>" >> hFlush stdout
      t <- pCommand <$> getLine
      (result,js') <- runStateT (feeds [t] k) js
      case result of
        Right () -> do
          env' <- execStateT fin env
          return $ (Right (), env')
        Left (k',_) -> go k' fin js' env

