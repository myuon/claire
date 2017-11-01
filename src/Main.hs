module Main where

import Control.Monad
import qualified Data.Sequence as S
import Text.Trifecta hiding (Source)
import System.IO
import Claire

main :: IO ()
main = forever $ do
  putStr "thm>" >> hFlush stdout
  Success fml <- pFormula <$> getLine

  run [Judgement S.Empty (S.singleton fml)]
  where
    run js = do
      putStrLn $ "goal>" ++ show (head js)
      when (length js >= 2) $ putStr $ "...and " ++ show (length js - 1) ++ " more goals"

      putStr "command>" >> hFlush stdout
      Success com <- pCommand <$> getLine
      case com of
        Apply rs -> 
          case checker rs js of
            Left (r,j) -> putStrLn ("Cannot apply " ++ show r ++ " to " ++ show j) >> run js
            Right [] -> putStrLn "QED."
            Right js' -> run js'
        Pick -> return ()


