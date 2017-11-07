module Claire.Checker where

import qualified Data.Map as M
import qualified Data.Sequence as S
import Claire.Laire

newtype Env = Env { getEnv :: M.Map ThmIndex Formula } deriving Show

insertThm :: ThmIndex -> Formula -> Env -> Env
insertThm idx fml (Env m) = Env $ M.insert idx fml m

defEnv :: Env
defEnv = Env M.empty


judge :: Env -> [Rule] -> [Judgement] -> Either (Rule, [Judgement]) [Judgement]
judge thms rs js = foldl (\m r -> m >>= go r) (Right js) rs where
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

checker :: Env -> Proof -> [Judgement] -> Either (Command, [Judgement]) [Judgement]
checker env (Proof coms) js = foldl (\m r -> m >>= go r) (Right js) coms where
  go c [] = Left (c,[])
  go (Apply rs) js = either (\(r,js) -> Left (Apply [r],js)) Right $ judge env rs js
  go (Use n) (Judgement assms props : js) = Right $ Judgement (assms S.:|> getEnv env M.! n) props : js

claire :: Env -> Laire -> Either () Env
claire env (Laire decls) = foldl (\m r -> m >>= go r) (Right env) decls where
  go (ThmD i fml p) env = case checker env p [Judgement S.empty (S.singleton fml)] of
    Right [] -> Right $ insertThm i fml env
    Left p -> error $ show p
  go (AxiomD i fml) env = Right $ insertThm i fml env

