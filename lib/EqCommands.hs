module EqCommands where

import Control.Monad.State.Strict
import Control.Monad.Catch
import Claire

data EqComError
  = WrongArgument Argument
  deriving Show

instance Exception EqComError

{-

thm: eq(a,b)
goal: assms |- P(a), props

rewrite :: Env -> Argument -> [Judgement] -> IO [Judgement]
rewrite env (ArgIdents [(i,ps)]) (js@(Judgement assms props:_)) = execStateT (comrunner env coms) js
  where
    coms =
      [ Apply [ImpL]
      , Use i ps
      , NewCommand "assumption" ArgEmpty
      ]
rewrite env arg _ = throwM $ WrongArgument arg
-}

refl :: Env -> Argument -> [Judgement] -> IO [Judgement]
refl env (ArgTerms [t]) js = execStateT (comrunner env coms) js
  where
    coms =
      [ Apply [Cut (pFormula "Forall r. eq(r,r)")]
      , Use "refl" [("eq", PredFun ["x"] $ PredFml $ pFormula "eq(x,x)")]
      , Apply [ForallR "r"]
      , NewCommand "assumption" ArgEmpty
      , Apply [ForallL t]
      , NewCommand "assumption" ArgEmpty
      ]
refl env arg _ = throwM $ WrongArgument arg

export_command =
  [ ("refl", refl)
  ]

export_decl = []

