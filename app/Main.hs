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
      seq env $ mapM_ putStrLn $
        [ "==========="
        , "=== QED ==="
        , "==========="
        , ""
        ]
      mapM_ print $ M.assocs $ getEnv env
    False -> do
      mapM_ putStrLn $
        [ "========================="
        , "=== Welcome to Claire ==="
        , "========================="
        , ""
        ]
      clairepl defEnv

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

clairepl :: Env -> IO ()
clairepl env = go env toplevelM where
  go :: Env -> Coroutine (DeclSuspender IO) (StateT Env IO) () -> IO ()
  go env k = do
    (result,env') <- flip runStateT env $ resume k
    putStrLn $ "env: " ++ show env'
  
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

