module Claire.Checker where

import qualified Data.Sequence as S
import Text.Trifecta
import Claire.FOL

checker' :: [Rule] -> Formula -> Either (Rule, Judgement) [Judgement]
checker' rs f = checker rs [Judgement S.Empty (S.singleton f)]

checker :: [Rule] -> [Judgement] -> Either (Rule, Judgement) [Judgement]
checker = go where
  go [] [] = Right []
  go (r:_) [] = Left (r,Judgement S.Empty S.Empty)
  go [] js = Right js

  go (I : rs) (Judgement assms props : js) | S.length assms == 1 && assms == props = go rs js
  go (Cut i j fml : rs) (Judgement assms props : js) = go rs (Judgement (S.take i assms) (S.take j props S.:|> fml) : Judgement (fml S.<| S.drop i assms) (S.drop j props) : js)
  go (AndL1 : rs) (Judgement (assms S.:|> (a :/\: b)) props : js) = go rs (Judgement (assms S.:|> a) props : js)
  go (AndL2 : rs) (Judgement (assms S.:|> (a :/\: b)) props : js) = go rs (Judgement (assms S.:|> b) props : js)
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

data Command
  = Apply [Rule]
  | Pick
  deriving (Eq, Show)

pCommand :: String -> Result Command
pCommand = parseString parser mempty where
  parser = choice [papply, ppick]

  papply = do
    symbol "apply"
    Apply <$> pRule
  ppick = symbol "pick" *> return Pick

  pRule :: Parser [Rule]
  pRule = (fmap read $ some $ noneOf ";") `sepBy` (symbol ";")

