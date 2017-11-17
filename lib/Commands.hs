module Commands where

import qualified Data.Sequence as S
import Data.List
import GHC.Exts (toList)
import Claire

onlyL :: Int -> Int -> [Rule]
onlyL i n = concat $ replicate (n-i-1) [WL] ++ replicate i [PL 0, WL]

onlyR :: Int -> Int -> [Rule]
onlyR i n = concat $ replicate i [WR] ++ replicate (n-i-1) [PR 1, WR]

assumption :: Env -> [Judgement] -> Either String [Judgement]
assumption env (js@(Judgement assms props:_)) = case S.findIndexL (`elem` toList assms) props of
  Nothing -> Left $ "The goal cannot be solved from its assumption: " ++ show js
  Just i ->
    let Just j = elemIndex (toList props !! i) (toList assms)
    in either (\_ -> Left "Failed to apply assumption") Right $ judge env (onlyR i (S.length props) ++ onlyL j (S.length assms) ++ [I]) js

export =
  [ ("assumption", assumption)
  ]

