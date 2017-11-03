module Claire.Laire.Syntax where

import Data.Set as S

type VSymbol = String
type FSymbol = String
type PSymbol = String

data Term = Var VSymbol | Func FSymbol [Term] deriving (Eq, Show)

data Formula
  = Pred PSymbol [Term]
  | Top
  | Bottom
  | Formula :/\: Formula
  | Formula :\/: Formula
  | Formula :->: Formula
  | Forall VSymbol Formula
  | Exist VSymbol Formula
  deriving (Eq, Show)

pattern Const c = Pred c []
pattern Neg a = a :->: Bottom

fv :: Formula -> S.Set VSymbol
fv = go where
  fvt (Var v) = S.singleton v
  fvt (Func _ ts) = S.unions $ fmap fvt ts
  
  go (Pred p ts) = S.unions $ fmap fvt ts
  go Top = S.empty
  go Bottom = S.empty
  go (f1 :/\: f2) = S.union (fv f1) (fv f2)
  go (f1 :\/: f2) = S.union (fv f1) (fv f2)
  go (f1 :->: f2) = S.union (fv f1) (fv f2)
  go (Forall v f) = S.delete v $ fv f
  go (Exist v f) = S.delete v $ fv f

substTerm :: Term -> Term -> Formula -> Formula
substTerm t t' = go where
  go (Pred p ts) = Pred p $ go' ts where
    go' [] = []
    go' (tm:tms) | tm == t = t' : go' tms
    go' (tm:tms) = tm : go' tms
  go Top = Top
  go Bottom = Bottom
  go (f1 :/\: f2) = go f1 :/\: go f2
  go (f1 :\/: f2) = go f1 :\/: go f2
  go (f1 :->: f2) = go f1 :->: go f2
  go (Forall x fml) = Forall x (go fml)
  go (Exist x fml) = Exist x (go fml)


