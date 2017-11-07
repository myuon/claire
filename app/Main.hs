{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE Strict #-}
module Main where

import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.State.Strict
import Control.Monad.Catch
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

runrepl :: Env -> Coroutine (Await Decl) (StateT Env IO) () -> IO ()
runrepl env k = do
  (result,env') <- runStateT (resume k) env `catch` \(ProofNotFinished k fin coms js) -> go k fin js env
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
        Right () -> fmap (\(x,y) -> (Right x,y)) $ runStateT fin env
        Left (k',_) -> go k' fin js' env

