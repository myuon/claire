module Commands where

import Control.Monad.State.Strict
import Control.Monad.Catch
import Data.List
import GHC.Exts (toList)
import Claire

data BasicComError
  = CannotSolve [Judgement]
  | FailedToApply
  | WrongArgument Argument
  | WrongArguments [Argument]
  deriving Show

instance Exception BasicComError

onlyL :: Int -> Int -> [Rule]
onlyL i n = concat $ replicate i [WL] ++ replicate (n-i-1) [PL 1, WL]

onlyR :: Int -> Int -> [Rule]
onlyR i n = concat $ replicate i [WR] ++ replicate (n-i-1) [PR 1, WR]

assumption :: Env -> Argument -> [Judgement] -> [Command]
assumption env ArgEmpty (js@(Judgement assms props:_)) = case findIndex (`elem` toList assms) props of
  Nothing -> throwM $ CannotSolve js
  Just i ->
    let Just j = elemIndex (toList props !! i) (toList assms)
    in return $ Apply $ onlyR i (length props) ++ onlyL j (length assms) ++ [I]
assumption env arg _ = throwM $ WrongArgument arg

{-| implyR

thm: a ==> b
goal: assms |- b, props

use thm
  assms, a ==> b |- b, props
apply ImpL
  assms |- a, b, props
  assms, b |- b, props
defer
  assms, b |- b, props
  assms |- a, b, props
assumption
  assms |- a, b, props
apply (PR 1, WR)
  assms |- a, props
-}
implyR :: Env -> Argument -> [Judgement] -> [Command]
implyR env (ArgIdents [(i,ps)]) js = Use i ps : implyR env ArgEmpty js
implyR env ArgEmpty _ = coms where
  coms =
    [ Apply [ImpL]
    , NewCommand "defer" ArgEmpty
    , NewCommand "assumption" ArgEmpty
    , Apply [PR 1, WR]
    ]
implyR env arg _ = throwM $ WrongArgument arg

{-| implyL

thm: a ==> b
goal: assms, a |- props

use thm
  assms, a, a ==> b |- props
apply ImpL
  assms, a |- a, props
  assms, a, b |- props
assumption
  assms, a, b |- props
apply (PL 1, WL)
  assms, b |- props
-}
implyL :: Env -> Argument -> [Judgement] -> [Command]
implyL env (ArgIdents [(i,ps)]) js = Use i ps : implyL env ArgEmpty js
implyL env ArgEmpty js = coms where
  coms =
    [ Apply [ImpL]
    , NewCommand "assumption" ArgEmpty
    , Apply [PL 1, WL]
    ]
implyL env arg _ = throwM $ WrongArgument arg

{-| genR

goal: assms |- P(a), props

apply Cut [Forall a. P(a)]
  assms |- Forall a. P(a), P(a), props
  assms, Forall a. P(a) |- P(a), props
defer
  assms, Forall a. P(a) |- P(a), props
  assms, |- Forall a. P(a), P(a), props
apply (ForallL [a])
  assms, P(a) |- P(a), props
  assms, |- Forall a. P(a), P(a), props
assumption
  assms, |- Forall a. P(a), P(a), props
apply (PR 1, WR)
  assms, |- Forall a. P(a), props
-}
genR :: Env -> Argument -> [Judgement] -> [Command]
genR env (ArgIdents [(i,[])]) (js@(Judgement _ (p:_):_)) = coms where
  coms =
    [ Apply [Cut $ Forall i p]
    , NewCommand "defer" ArgEmpty
    , Apply [ForallL (Var i)]
    , NewCommand "assumption" ArgEmpty
    , Apply [PR 1, WR]
    ]
genR env arg _ = throwM $ WrongArgument arg

{-| genL

goal: assms, P(a) |- props

apply Cut [Forall a. P(a)]
  assms, P(a) |- Forall a. P(a), props
  assms, P(a), Forall a. P(a) |- props
apply (ForallR [a])
  assms, P(a) |- P(a), props
  assms, P(a), Forall a. P(a) |- props
assumption
  assms, P(a), Forall a. P(a) |- props
apply (PL 1, WR)
  assms, Forall a. P(a) |- props
-}
genL :: Env -> Argument -> [Judgement] -> [Command]
genL env (ArgIdents [(i,[])]) (js@(Judgement (p:ps) _:_)) = 
  [ Apply [Cut $ Forall i p]
  , Apply [ForallR i]
  , NewCommand "assumption" ArgEmpty
  , Apply [PL (length ps), WL]
  ]
genL env arg _ = throwM $ WrongArgument arg

{-| absR

goal: assms, a |- b, props

apply Cut [a ==> b]
  assms, a |- a ==> b, b, props
  assms, a, a ==> b |- b, props
defer
  assms, a, a ==> b |- b, props
  assms, a |- a ==> b, b, props
apply ImpL
  assms, a |- a, b, props
  assms, a, b |- b, props
  assms, a |- a ==> b, b, props
assumption [2]
  assms, a |- a ==> b, b, props
apply (PR 1, WR, WL)
  assms |- a ==> b, props
-}

absL :: Env -> Argument -> [Judgement] -> [Command]
absL env ArgEmpty (js@(Judgement (a:_) (b:_):_)) =
  [ Apply [Cut $ a :==>: b]
  , NewCommand "defer" ArgEmpty
  , Apply [ImpL]
  , NewCommand "assumption" ArgEmpty
  , NewCommand "assumption" ArgEmpty
  , Apply [PR 1, WR, WL]
  ]

export_command :: [(String, Env -> Argument -> [Judgement] -> [Command])]
export_command =
  [ ("assumption", assumption)
  , ("implyR", implyR)
  , ("implyL", implyL)
  , ("genR", genR)
  , ("genL", genL)
  , ("absL", absL)
  ]

---------------------------------------------

definition :: [Argument] -> [Decl]
definition [ArgTyped i typ, ArgPreds [PredFml body]] =
  [ ConstD i typ
  , AxiomD (i ++ "_def") body
  ]
definition arg = throwM $ WrongArguments arg

export_decl =
  [ ("definition", definition)
  ]

