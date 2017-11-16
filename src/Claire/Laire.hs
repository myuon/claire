module Claire.Laire
  ( Rule(..)
  , Judgement(..)

  , module Claire.Laire.Syntax
  , pLaire
  , pDecl
  , pCommand
  , pFormula
  , pTerm

  , Env(..)
  , insertThm
  , print_proof
  , defEnv
  , fp
  , metagen
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Claire.Laire.Syntax
import Claire.Laire.Lexer
import Claire.Laire.Parser

pLaire :: String -> Laire
pLaire = laireparser . alexScanTokens

pDecl :: String -> Decl
pDecl = declparser . alexScanTokens

pCommand :: String -> Command
pCommand = comparser . alexScanTokens

pFormula :: String -> Formula
pFormula = folparser . alexScanTokens

pTerm :: String -> Term
pTerm = termparser . alexScanTokens


data Env
  = Env
  { thms :: M.Map ThmIndex Formula
  , preds :: M.Map Ident Int
  , proof :: [(Command, String)]
  }
  deriving Show

insertThm :: ThmIndex -> Formula -> Env -> Env
insertThm idx fml env = env { thms = M.insert idx (metagen env fml) (thms env) }

defEnv :: Env
defEnv = Env M.empty M.empty []

print_proof :: Env -> String
print_proof env = unlines $
  [ "= proof of the previous theorem ="
  , "proof" ]
  ++ map (\x -> "  " ++ snd x) (filter (not . ignore . fst) $ proof env)
  ++ [ "qed" ]

  where
    ignore (NoApply _) = True
    ignore _ = False

fp :: Env -> Formula -> S.Set Ident
fp env = go where
  go (Pred p ts)
    | p `elem` M.keys (preds env) = S.empty
    | otherwise = S.singleton p
  go Top = S.empty
  go Bottom = S.empty
  go (fml1 :/\: fml2) = go fml1 `S.union` go fml2
  go (fml1 :\/: fml2) = go fml1 `S.union` go fml2
  go (fml1 :==>: fml2) = go fml1 `S.union` go fml2
  go (Forall _ fml) = go fml
  go (Exist _ fml) = go fml

metagen :: Env -> Formula -> Formula
metagen env = go where
  go (Pred p ts)
    | p `elem` M.keys (preds env) = Pred p ts
    | otherwise = Pred ('?' : p) ts
  go Top = Top
  go Bottom = Bottom
  go (fml1 :/\: fml2) = go fml1 :/\: go fml2
  go (fml1 :\/: fml2) = go fml1 :\/: go fml2
  go (fml1 :==>: fml2) = go fml1 :==>: go fml2
  go (Forall v fml) = Forall v $ go fml
  go (Exist v fml) = Exist v $ go fml

