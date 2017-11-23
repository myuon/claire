{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Claire.Syntax.FOL where

import Control.Monad
import Control.Monad.Catch
import qualified Data.Set as S

type Ident = String

data Term = Var Ident | Func Ident [Term] deriving (Eq, Show)

data TypeForm a
  = VarT a
  | ConT Ident [TypeForm a]
  | ArrT (TypeForm a) (TypeForm a)
  | Prop
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Type = TypeForm Ident

data Formula
  = Pred Ident [Term]
  | Top
  | Bottom
  | Formula :/\: Formula
  | Formula :\/: Formula
  | Formula :==>: Formula
  | Forall Ident Formula
  | Exist Ident Formula
  deriving (Eq, Show)

pattern Const c = Pred c []
pattern Neg a = a :==>: Bottom

data Predicate
  = PredFun [Ident] Predicate
  | PredFml Formula
  deriving (Show)

fvT :: Ord a => TypeForm a -> S.Set a
fvT = go where
  go (VarT v) = S.singleton v
  go (ConT _ ts) = S.unions $ fmap fvT ts
  go (ArrT t1 t2) = go t1 `S.union` go t2
  go Prop = S.empty

substType :: Eq a => a -> TypeForm a -> TypeForm a -> TypeForm a
substType x t' = go where
  go (VarT y)
    | x == y = t'
    | otherwise = VarT y
  go (ConT y ts) = ConT y (fmap go ts)
  go (ArrT y1 y2) = ArrT (go y1) (go y2)
  go Prop = Prop

fv :: Formula -> S.Set Ident
fv = go where
  fvt (Var v) = S.singleton v
  fvt (Func _ ts) = S.unions $ fmap fvt ts
  
  go (Pred p ts) = S.unions $ fmap fvt ts
  go Top = S.empty
  go Bottom = S.empty
  go (f1 :/\: f2) = S.union (fv f1) (fv f2)
  go (f1 :\/: f2) = S.union (fv f1) (fv f2)
  go (f1 :==>: f2) = S.union (fv f1) (fv f2)
  go (Forall v f) = S.delete v $ fv f
  go (Exist v f) = S.delete v $ fv f

substTerm :: Ident -> Term -> Formula -> Formula
substTerm idt t' = go where
  got (Var i)
    | i == idt = t'
    | otherwise = Var i
  got (Func f ts) = Func f $ fmap got ts
  
  go (Pred p ts) = Pred p $ fmap got ts
  go Top = Top
  go Bottom = Bottom
  go (f1 :/\: f2) = go f1 :/\: go f2
  go (f1 :\/: f2) = go f1 :\/: go f2
  go (f1 :==>: f2) = go f1 :==>: go f2
  go (Forall x fml) = Forall x (go fml)
  go (Exist x fml) = Exist x (go fml)

data SubstError
  = ArgumentsNotFullyApplied Predicate
  | CannotApplyToFormula [Term] Formula
  deriving Show

instance Exception SubstError

substPred :: MonadThrow m => Ident -> Predicate -> Formula -> m Formula
substPred idt pred = go where
  go (z@(Pred idt' ts))
    | idt == idt' = beta ts pred
    | otherwise = return z
  go Top = return Top
  go Bottom = return Bottom
  go (fml1 :/\: fml2) = liftM2 (:/\:) (go fml1) (go fml2)
  go (fml1 :\/: fml2) = liftM2 (:\/:) (go fml1) (go fml2)
  go (fml1 :==>: fml2) = liftM2 (:==>:) (go fml1) (go fml2)
  go (Forall v fml) = Forall v <$> (go fml)
  go (Exist v fml) = Exist v <$> (go fml)

  beta xs (PredFun [] p) = beta xs p
  beta [] (z@(PredFun _ _)) = throwM $ ArgumentsNotFullyApplied z
  beta [] (PredFml fml) = return fml
  beta (x:xs) (PredFun (t:ts) fml) = beta xs (PredFun ts $ sbterm t x fml)
  beta xs (PredFml fml) = throwM $ CannotApplyToFormula xs fml

  sbterm t x (PredFun ys fml) = PredFun ys $ sbterm t x fml
  sbterm t x (PredFml fml) = PredFml $ substTerm t x fml

generalize :: Formula -> Formula
generalize fml = S.foldl (\f i -> Forall i f) fml (fv fml)

