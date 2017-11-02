module Main where

import Control.Monad
import qualified Data.Map as M
import Text.Trifecta hiding (Source)
import Text.PrettyPrint.ANSI.Leijen (putDoc)
import System.IO
import Claire

main :: IO ()
main = claire (Thms M.empty)

claire :: Thms -> IO ()
claire thms = do
  putStr "thm>" >> hFlush stdout
  fml <- pFormula <$> getLine
  thms' <- prover fml thms
  claire thms'

prover :: Formula -> Thms -> IO Thms
prover origfml thms = run [Judgement M.empty origfml] where
  run :: [Judgement] -> IO Thms
  run js = do
    putStrLn $ "goal>" ++ show (head js)
    when (length js >= 2) $ putStrLn $ "...and " ++ show (length js - 1) ++ " more goals"

    putStr "command>" >> hFlush stdout
    mcom <- pCommand <$> getLine
    case mcom of
      Success com -> 
        case com of
          Apply rs -> 
            case checker thms rs js of
              Left (r,j) -> do
                putStrLn ("Cannot apply " ++ show r ++ " to " ++ show j)
                run js

              Right [] -> do
                putStrLn $ "Proved: " ++ show origfml
                putStr "Would you like to name this theorem? [Enter to skip/type thm name]>" >> hFlush stdout
                name <- getLine
                return $ case name of
                  "" -> thms
                  n -> insertThm n origfml thms

              Right js' -> run js'

      Failure err -> do
        putDoc $ _errDoc err
        run js

