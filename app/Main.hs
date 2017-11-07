module Main where

import Control.Monad.Coroutine
import Control.Monad.State.Strict
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

runrepl :: Env -> Coroutine (DeclSuspender IO) (StateT Env IO) () -> IO ()
runrepl env k = do
  (result,env') <- flip runStateT env $ resume k
  putStrLn $ "env: " ++ show env'
  
  case result of
    Right () -> runrepl env' k
    Left (DeclAwait k) -> do
      putStr "decl>" >> hFlush stdout
      t <- pDecl <$> getLine
      runrepl env' (k t)
    Left (ProofNotFinished js cont) -> do
      mapM_ print js
      putStr "command>" >> hFlush stdout
      t <- pCommand <$> getLine
      runrepl env' (cont t)
    Left (ComError (CannotApply r js _) cont) -> do
      putStrLn $ "Cannot apply " ++ show r ++ " to " ++ show js
      runrepl env' cont

