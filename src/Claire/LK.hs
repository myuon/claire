module Claire.LK where

import qualified Data.Sequence as S
import Text.Trifecta
import GHC.Exts (toList)

-- First-order logic
type VSymbol = String
type FSymbol = String
type PSymbol = String

data Term = Var VSymbol | Func FSymbol [Term] deriving (Eq, Show, Read)
data Formula
  = Pred PSymbol [Term]
  | Neg Formula
  | Formula :/\: Formula
  | Forall VSymbol Formula
  deriving (Eq, Show, Read)

pattern FmlTerm t = Pred "term" [t]
pattern (:-->:) fml1 fml2 = Neg ((Neg (Neg fml1)) :/\: Neg fml2)

subst :: Formula -> Term -> VSymbol -> Formula
subst (FmlTerm (Var v)) t x | v == x = FmlTerm t
subst (Pred p ts) t x = Pred p ts
subst (Neg fml) t x = Neg (subst fml t x)
subst (fml1 :/\: fml2) t x = subst fml1 t x :/\: subst fml2 t x
subst (Forall y fml) t x | x == y = Forall y fml
subst (Forall y fml) t x | otherwise = Forall y (subst fml t x)

pFormula :: String -> Result Formula
pFormula = parseString parser mempty where
  parser :: Parser Formula
  parser = choice [try por, try pand, try pimp, pfml]

  pfml = spaces *> choice [parens parser, pforall, pexist, pneg, FmlTerm . Var <$> pvar]

  pvar = some alphaNum

  pand = do
    fml1 <- pfml <* spaces
    symbol "/\\"
    fml2 <- parser <* spaces
    return $ fml1 :/\: fml2
  por = do
    fml1 <- pfml <* spaces
    symbol "\\/"
    fml2 <- parser <* spaces
    return $ Neg $ (Neg fml1) :/\: (Neg fml2)
  pimp = do
    fml1 <- pfml <* spaces
    symbol "->"
    fml2 <- parser <* spaces
    return $ fml1 :-->: fml2
  pneg = do
    symbol "~"
    pfml <- parser
    return $ Neg pfml
  pforall = do
    symbol "forall"
    v <- pvar <* spaces
    symbol "."
    fml <- parser
    return $ Forall v fml
  pexist = do
    symbol "exist"
    v <- pvar <* spaces
    symbol "."
    fml <- parser
    return $ Neg $ Forall v $ Neg fml

-- LK
data Rule
  -- axiom
  = I

  -- cut
  | Cut Int Int Formula

  -- left logical rules
  | AndL1 | AndL2 | NegL | ForallL Term

  -- right logical rules
  | AndR Int Int | NegR | ForallR VSymbol

  -- structual rules
  | WL | CL | PL Int Int
  | WR | CR | PR Int Int
  deriving (Eq, Show, Read)

-- Judgement xs ys <=> x1 .. xn |- y1 .. ym
data Judgement = Judgement (S.Seq Formula) (S.Seq Formula) deriving (Eq)

instance Show Judgement where
  show (Judgement assms props) = show (toList assms) ++ " |- " ++ show (toList props)

