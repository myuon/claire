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
      env <- claire defEnv . (\(Laire ds) -> ds) . pLaire =<< readFile (head xs)
      putStrLn "= Predicates ="
      mapM_ print $ M.assocs $ preds env
      putStrLn "= Proved Theorems ="
      mapM_ print $ M.assocs $ thms env
    False -> do
      mapM_ putStrLn $
        [ "========================="
        , "=== Welcome to Claire ==="
        , "========================="
        , ""
        ]
      env <- claire defEnv . (\(Laire ds) -> ds) . pLaire =<< readFile "lib/preliminaries.cl"
      clairepl env

clairepl :: Env -> IO ()
clairepl env = go env toplevelM where
  go :: Env -> Coroutine (DeclSuspender IO) (StateT Env IO) () -> IO ()
  go env k = do
    (result,env') <- flip runStateT env $ resume k
--    putStrLn $ "env: " ++ show env'
  
    case result of
      Right () -> go env' k
      Left (DeclAwait k) -> do
        putStr "decl>" >> hFlush stdout
        t <- pDecl <$> getLine
        go env' (k t)
      Left (ProofNotFinished js cont) -> do
        mapM_ print js
        putStr "command>" >> hFlush stdout
        t <- pCommand <$> getLine
        go env' (cont t)
      Left (ComError (CannotApply r js _) cont) -> do
        putStrLn $ "Cannot apply " ++ show r ++ " to " ++ show js
        go env' cont

