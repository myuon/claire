module Main where

import Control.Monad
import qualified Data.Sequence as S
import Text.Trifecta

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

pattern FTerm t = Pred "term" [t]

subst :: Formula -> Term -> VSymbol -> Formula
subst (FTerm (Var v)) t x | v == x = FTerm t
subst (Pred p ts) t x = Pred p ts
subst (Neg fml) t x = Neg (subst fml t x)
subst (fml1 :/\: fml2) t x = subst fml1 t x :/\: subst fml2 t x
subst (Forall y fml) t x | x == y = Forall y fml
subst (Forall y fml) t x | otherwise = Forall y (subst fml t x)

pFormula :: String -> Result Formula
pFormula = parseString parser mempty where
  parser :: Parser Formula
  parser = choice [try por, try pand, try pimp, pfml]

  pfml = spaces *> choice [parens parser, pforall, pneg, Pred "var" . return . Var <$> pvar]

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
    -- A --> B
    -- = ~A \/ B
    -- = ~ (~~A /\ ~B)
    fml1 <- pfml <* spaces
    symbol "->"
    fml2 <- parser <* spaces
    return $ Neg $ (Neg (Neg fml1)) :/\: Neg fml2
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
data Judgement = Judgement (S.Seq Formula) (S.Seq Formula) deriving (Eq, Show)

checker :: [Rule] -> [Judgement] -> Either (Rule, Judgement) [Judgement]
checker = go where
  go [] [] = Right []
  go (r:_) [] = Left (r,Judgement S.Empty S.Empty)
  go [] js = Right js

  go (I : rs) (Judgement assms props : js) | S.length assms == 1 && assms == props = go rs js
  go (Cut i j fml : rs) (Judgement assms props : js) = go rs (Judgement (S.take i assms) (S.take j props S.:|> fml) : Judgement (fml S.<| S.drop i assms) (S.drop j props) : js)
  go (AndL1 : rs) (Judgement (assms S.:|> (a :/\: b)) props : js) = go rs (Judgement (assms S.:|> a) props : js)
  go (AndL1 : rs) (Judgement (assms S.:|> (a :/\: b)) props : js) = go rs (Judgement (assms S.:|> b) props : js)
  go (NegL : rs) (Judgement (assms S.:|> Neg a) props : js) = go rs (Judgement assms (a S.:<| props) : js)
  go (ForallL t : rs) (Judgement (assms S.:|> Forall x a) props : js) = go rs (Judgement (assms S.:|> subst a t x) props : js)

  go (AndR i j : rs) (Judgement assms ((a :/\: b) S.:<| props) : js) = go rs (Judgement (S.take i assms) (a S.:<| S.take j props) : Judgement (S.drop i assms) (b S.:<| S.drop j props) : js)
  go (NegR : rs) (Judgement assms (Neg a S.:<| props) : js) = go rs (Judgement (assms S.:|> a) props : js)
  go (ForallR y : rs) (Judgement assms (Forall x a S.:<| props) : js) = go rs (Judgement assms (subst a (Var y) x S.:<| props) : js)

  go (WL : rs) (Judgement (assms S.:|> _) props : js) = go rs (Judgement assms props : js)
  go (CL : rs) (Judgement (assms S.:|> a) props : js) = go rs (Judgement (assms S.:|> a S.:|> a) props : js)
  go (PL i j : rs) (Judgement assms props : js) = go rs (Judgement (S.update i (S.index assms j) $ S.update j (S.index assms i) assms) props : js)
  go (WR : rs) (Judgement assms (_ S.:<| props) : js) = go rs (Judgement assms props : js)
  go (CR : rs) (Judgement assms (a S.:<| props) : js) = go rs (Judgement assms (a S.:<| a S.:<| props) : js)
  go (PR i j : rs) (Judgement assms props : js) = go rs (Judgement assms (S.update i (S.index props j) $ S.update j (S.index props i) props) : js)

  go (r:_) (j:_) = Left (r,j)

main :: IO ()
main = forever $ do
  putStr "thm>"
  Success p <- pFormula <$> getLine
  prove [Judgement S.Empty (S.singleton p)]

  where
    prove js = do
      putStr "goal>" >> print (head js)
      putStr $ "...and " ++ show (length js - 1) ++ " more goals"
      
      putStr "rule>"
      r <- read <$> getLine
      let Right js' = checker [r] js
      unless (null js') $ prove js'
      

