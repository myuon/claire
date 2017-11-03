module Claire.Checker where

import Control.Applicative
import qualified Data.Map as M
import qualified Data.Sequence as S
import Text.Trifecta
import Claire.FOL

checker' :: [Rule] -> Formula -> Either (Rule, [Judgement]) [Judgement]
checker' rs f = checker defThms rs [Judgement S.empty (S.singleton f)]

checker :: Thms -> [Rule] -> [Judgement] -> Either (Rule, [Judgement]) [Judgement]
checker thms rs js = foldl (\m r -> m >>= go r) (Right js) rs where
  go I (Judgement assms props : js) | S.length assms == 1 && assms == props = Right js
  go (Cut fml) (Judgement assms props : js) = Right $ Judgement assms (fml S.:<| props) : Judgement (assms S.:|> fml) props : js
  go AndL1 (Judgement (assms S.:|> (fa :/\: fb)) props : js) = Right $ Judgement (assms S.:|> fa) props : js
  go AndL2 (Judgement (assms S.:|> (fa :/\: fb)) props : js) = Right $ Judgement (assms S.:|> fb) props : js
  go AndR (Judgement assms ((fa :/\: fb) S.:<| props) : js) = Right $ Judgement assms (fa S.:<| props) : Judgement assms (fb S.:<| props) : js
  go OrL (Judgement (assms S.:|> (fa :\/: fb)) props : js) = Right $ Judgement (assms S.:|> fa) props : Judgement (assms S.:|> fb) props : js
  go OrR1 (Judgement assms ((fa :\/: fb) S.:<| props) : js) = Right $ Judgement assms (fa S.:<| props) : js
  go OrR2 (Judgement assms ((fa :\/: fb) S.:<| props) : js) = Right $ Judgement assms (fb S.:<| props) : js
  go ImpL (Judgement (assms S.:|> (fa :->: fb)) props : js) = Right $ Judgement assms (fa S.:<| props) : Judgement (assms S.:|> fb) props : js
  go ImpR (Judgement assms ((fa :->: fb) S.:<| props) : js) = Right $ Judgement (assms S.:|> fa) (fb S.:<| props) : js
  go BottomL (Judgement (assms S.:|> Bottom) props : js) = Right js
  go TopR (Judgement assms (Top S.:<| props) : js) = Right js
  go (ForallL t) (Judgement (assms S.:|> Forall x fml) props : js) = Right $ Judgement (assms S.:|> substTerm (Var x) t fml) props : js
  go (ForallR y) (Judgement assms (Forall x fml S.:<| props) : js) = Right $ Judgement assms (substTerm (Var x) (Var y) fml S.:<| props) : js
  go (ExistL y) (Judgement (assms S.:|> Exist x fml) props : js) = Right $ Judgement (assms S.:|> substTerm (Var x) (Var y) fml) props : js
  go (ExistR t) (Judgement assms (Exist x fml S.:<| props) : js) = Right $ Judgement assms (substTerm (Var x) t fml S.:<| props) : js

  go WL (Judgement (assms S.:|> _) props : js) = Right $ Judgement assms props : js
  go WR (Judgement assms (_ S.:<| props) : js) = Right $ Judgement assms props : js
  go CL (Judgement (assms S.:|> fml) props : js) = Right $ Judgement (assms S.:|> fml S.:|> fml) props : js
  go CR (Judgement assms (fml S.:<| props) : js) = Right $ Judgement assms (fml S.:<| fml S.:<| props) : js
  go (PL k) (Judgement assms props : js) | k < S.length assms = Right $ Judgement (S.deleteAt k assms S.:|> S.index assms k) props : js
  go (PR k) (Judgement assms props : js) | k < S.length props = Right $ Judgement assms (S.index props k S.:<| S.deleteAt k props) : js

  go r js = Left (r,js)

data Command
  = Apply [Rule]
  | Thm ThmIndex
  deriving (Eq, Show)

pCommand :: String -> Result Command
pCommand = parseString parser mempty where
  parser = choice $ fmap try [pthm, papply]

  pthm = do
    symbol "thm"
    Thm <$> some letter

  papply = do
--    symbol "apply"
    Apply <$> pRules
--  ppick = symbol "pick" *> return Pick

  pRules :: Parser [Rule]
  pRules = prule `sepBy` (symbol ";")

  prule = choice $ fmap try $
   [ symbol "I" *> spaces *> eof *> return I
   , symbol "Cut" *> (Cut <$> parens (pFormula <$> some (noneOf ")")))
   , symbol "AndL1" *> return AndL1
   , symbol "AndL2" *> return AndL2
   , symbol "AndR" *> return AndR
   , symbol "OrL" *> return OrL
   , symbol "OrR1" *> return OrR1
   , symbol "OrR2" *> return OrR2
   , symbol "ImpL" *> return ImpL
   , symbol "ImpR" *> return ImpR
   , symbol "BottomL" *> return BottomL
   , symbol "TopR" *> return TopR
   , symbol "ForallL" *> (ForallL <$> parens (pTerm <$> some (noneOf ")")))
   , symbol "ForallR" *> (ForallR <$> some letter)
   , symbol "ExistL" *> (ExistL <$> some letter)
   , symbol "ExistR" *> (ExistR <$> parens (pTerm <$> some (noneOf ")")))
   , symbol "WL" *> return WL
   , symbol "WR" *> return WR
   , symbol "CL" *> return CL
   , symbol "CR" *> return CR
   , symbol "PL" *> (PL <$> (read <$> some digit))
   , symbol "PR" *> (PR <$> (read <$> some digit))
   ]

type ThmIndex = String

newtype Thms = Thms { getThms :: M.Map ThmIndex Formula }

insertThm :: ThmIndex -> Formula -> Thms -> Thms
insertThm idx fml (Thms m) = Thms $ M.insert idx fml m

defThms :: Thms
defThms = Thms M.empty

