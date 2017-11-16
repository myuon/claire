module Main where

import Control.Monad.Coroutine
import Control.Monad.State.Strict
import Control.Exception.Base
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
      clairepl env
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
        t <- safep (putStr "decl>" >> hFlush stdout) pDecl
        go env' (k t)
      Left (ProofNotFinished js cont) -> do
        mapM_ print js
        (t,raw) <- safep (putStr "command>" >> hFlush stdout) (\s -> let s' = pCommand s in s' `seq` (s',s))
        let addProof env k = env { proof = proof env ++ [k] }
        go (addProof env' (t,raw)) (cont t)
      Left (ComError (CannotApply r js _) cont) -> do
        putStrLn $ "Cannot apply " ++ show r ++ " to " ++ show js
        let unaddProof env | length (proof env) >= 1 = env { proof = tail (proof env) }
            unaddProof env = env
        go (unaddProof env') cont

  safep :: IO () -> (String -> a) -> IO a
  safep ma p = ma >> (p <$!> getLine) `catch` (\err -> print (err :: ErrorCall) >> safep ma p)

