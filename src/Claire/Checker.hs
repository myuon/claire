module Claire.Checker where

import Control.Applicative
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Trifecta
import Claire.FOL

checker' :: [Rule] -> Formula -> Either ([Rule], [Judgement]) [Judgement]
checker' rs f = checker defThms rs [Judgement M.empty f]

checker :: Thms -> [Rule] -> [Judgement] -> Either ([Rule], [Judgement]) [Judgement]
checker thms = go where
  go (Init k:rs) (Judgement assms prop : js) | k `M.member` assms && assms M.! k == prop = go rs js
  go (Init k:rs) (Judgement assms prop : js) | k `M.member` (getThms thms) && getThms thms M.! k == prop = go rs js
  go (Abs:rs) (Judgement assms prop : js) = go rs (Judgement (addAssm (Neg prop) assms) Bottom : js)
  go (TopI:rs) (Judgement assms prop : js) | prop == Bottom = go rs js
  go (BottomE:rs) (Judgement assms prop : js) = go rs (Judgement assms Bottom : js)
  go (AndI:rs) (Judgement assms (prop1 :/\: prop2) : js) = go rs (Judgement assms prop1 : Judgement assms prop2 : js)
  go (AndE1 fml:rs) (Judgement assms prop : js) = go rs (Judgement assms (prop :/\: fml) : js)
  go (AndE2 fml:rs) (Judgement assms prop : js) = go rs (Judgement assms (fml :/\: prop) : js)
  go (OrI1:rs) (Judgement assms (prop1 :\/: prop2) : js) = go rs (Judgement assms prop1 : js)
  go (OrI2:rs) (Judgement assms (prop1 :\/: prop2) : js) = go rs (Judgement assms prop2 : js)
  go (OrE fml fml':rs) (Judgement assms prop : js) = go rs (Judgement assms (fml :\/: fml') : Judgement (addAssm fml assms) prop : Judgement (addAssm fml' assms) prop : js)
  go (ImpI:rs) (Judgement assms (fml :->: fml') : js) = go rs (Judgement (addAssm fml assms) fml' : js)
  go (ImpE fml:rs) (Judgement assms prop : js) = go rs (Judgement assms (fml :->: prop) : Judgement assms fml : js)
  go (ForallI:rs) (Judgement assms (Forall x prop) : js) | S.notMember x (S.unions $ fmap fv $ M.elems assms) = go rs (Judgement assms prop : js)
  go (ForallE t x:rs) (Judgement assms prop : js) = go rs (Judgement assms (substTerm t (Var x) prop) : js)
  go (ExistI t:rs) (Judgement assms (Exist x prop) : js) = go rs (Judgement assms (substTerm (Var x) t prop) : js)
  go (ExistE (Exist x fml):rs) (Judgement assms prop : js) | S.notMember x (S.unions $ fmap fv $ M.elems assms) && S.notMember x (fv prop) = go rs (Judgement assms (Exist x fml) : Judgement (addAssm fml assms) prop : js)
  go [] js = Right js
  go rs js = Left (rs, js)

data Command
  = Apply [Rule]
  | Pick
  deriving (Eq, Show)

pCommand :: String -> Result Command
pCommand = parseString parser mempty where
  parser = choice [papply]

  papply = do
--    symbol "apply"
    Apply <$> pRules
--  ppick = symbol "pick" *> return Pick

  pRules :: Parser [Rule]
  pRules = prule `sepBy` (symbol ";")

  prule = choice
   [ symbol "init" *> (Init <$> some (letter <|> digit))
   , symbol "abs" *> return Abs
   , symbol "topI" *> return TopI
   , symbol "bottomE" *> return BottomE
   , symbol "andI" *> return AndI
   , symbol "andE1" *> (AndE1 <$> parens (pFormula <$> some (noneOf ")")))
   , symbol "andE2" *> (AndE2 <$> parens (pFormula <$> some (noneOf ")")))
   , symbol "orI1" *> return OrI1
   , symbol "orI2" *> return OrI2
   , symbol "impI" *> return ImpI
   , symbol "impE" *> (ImpE <$> parens (pFormula <$> some (noneOf ")")))
   , symbol "forallI" *> return ForallI
   , symbol "forallE" *> (ForallE <$> parens (pTerm <$> some (noneOf ")")) <*> some (letter <|> digit))
   , symbol "existI" *> (ExistI <$> parens (pTerm <$> some (noneOf ")")))
   , symbol "existE" *> (ExistE <$> parens (pFormula <$> some (noneOf ")")))
   ]

type ThmIndex = String

newtype Thms = Thms { getThms :: M.Map ThmIndex Formula }

insertThm :: ThmIndex -> Formula -> Thms -> Thms
insertThm idx fml (Thms m) = Thms $ M.insert idx fml m

defThms :: Thms
defThms = Thms M.empty

