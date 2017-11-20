module Claire.Typecheck where

import Control.Monad.Catch
import qualified Data.Map as M

import Claire.Syntax
import Claire.Env

data TypeInferenceError
  = FormulaTypeMismatch Formula Type Type
  | TermTypeMismatch Term Type Type
  | NotFound Ident
  deriving (Show)

instance Exception TypeInferenceError

inferT :: Env -> Term -> Either TypeInferenceError Type
inferT env = go where
  go (Var v) | v `M.member` terms env = do
    return $ terms env M.! v
  go (Var v) = Left $ NotFound v
  go (Func v ts) | v `M.member` terms env = do
    let vty = terms env M.! v
    funtype env vty ts
  go (Func v ts) = Left $ NotFound v

expect k t1 t2
  | t1 == t2 = return t1
  | otherwise = Left $ k t1 t2

funtype env ty [] = return ty
funtype env (ArrT ty1 ty2) (t:ts) = do
  expect (TermTypeMismatch t) ty1 =<< inferT env t
  funtype env ty2 ts

infer :: Env -> Formula -> Either TypeInferenceError Type
infer env = go where
  go (Pred p ts) | p `M.member` preds env = do
    typ <- funtype env (preds env M.! p) ts
    expect (FormulaTypeMismatch (Pred p ts)) Prop typ
  go (Pred p ts) = Left $ NotFound p
  go Top = return Prop
  go Bottom = return Prop
  go (fml1 :/\: fml2) = do
    t1 <- go fml1
    expect (FormulaTypeMismatch fml1) Prop t1
    t2 <- go fml2
    expect (FormulaTypeMismatch fml2) Prop t2
  go (fml1 :\/: fml2) = do
    t1 <- go fml1
    expect (FormulaTypeMismatch fml1) Prop t1
    t2 <- go fml2
    expect (FormulaTypeMismatch fml2) Prop t2
  go (fml1 :==>: fml2) = do
    t1 <- go fml1
    expect (FormulaTypeMismatch fml1) Prop t1
    t2 <- go fml2
    expect (FormulaTypeMismatch fml2) Prop t2
  go (Forall v fml) = do
    t <- go fml
    expect (FormulaTypeMismatch fml) Prop t
  go (Exist v fml) = do
    t <- go fml
    expect (FormulaTypeMismatch fml) Prop t
