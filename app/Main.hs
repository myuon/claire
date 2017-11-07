module Main where

import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.State
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

runrepl :: Env -> Coroutine (Await Decl) (StateT Env IO) ()  -> IO ()
runrepl env k = do
  (result,env') <- runStateT (resume k) env
  putStrLn $ "env: " ++ show env'
  
  case result of
    Right () -> return ()
    Left (Await k) -> do
      putStr "decl>" >> hFlush stdout
      t <- pDecl <$> getLine

      runrepl env' (k t)

