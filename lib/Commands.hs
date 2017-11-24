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

assumption :: Env -> Argument -> [Judgement] -> IO [Judgement]
assumption env ArgEmpty (js@(Judgement assms props:_)) = case findIndex (`elem` toList assms) props of
  Nothing -> throwM $ CannotSolve js
  Just i ->
    let Just j = elemIndex (toList props !! i) (toList assms)
    in return $ either (\_ -> throwM $ FailedToApply) id $ judge env (onlyR i (length props) ++ onlyL j (length assms) ++ [I]) js
assumption env arg _ = throwM $ WrongArgument arg

defer :: Env -> Argument -> [Judgement] -> IO [Judgement]
defer env ArgEmpty (j:js) = return $ js ++ [j]
defer env arg _ = throwM $ WrongArgument arg

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
implyR :: Env -> Argument -> [Judgement] -> IO [Judgement]
implyR env (ArgIdents [(i,ps)]) js = implyR env ArgEmpty =<< execStateT (comrunner env [Use i ps]) js
implyR env ArgEmpty js = execStateT (comrunner env coms) js
  where
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
implyL :: Env -> Argument -> [Judgement] -> IO [Judgement]
implyL env ArgEmpty js = execStateT (comrunner env coms) js
  where
    coms =
      [ Apply [ImpL]
      , NewCommand "assumption" ArgEmpty
      , Apply [PL 1, WL]
      ]
implyL env (ArgIdents [(i,ps)]) js = implyL env ArgEmpty =<< execStateT (comrunner env [Use i ps]) js
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
genR :: Env -> Argument -> [Judgement] -> IO [Judgement]
genR env (ArgIdents [(i,[])]) (js@(Judgement _ (p:_):_)) = execStateT (comrunner env coms) js
  where
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
genL :: Env -> Argument -> [Judgement] -> IO [Judgement]
genL env (ArgIdents [(i,[])]) (js@(Judgement (p:ps) _:_)) = execStateT (comrunner env coms) js
  where
    coms =
      [ Apply [Cut $ Forall i p]
      , Apply [ForallR i]
      , NewCommand "assumption" ArgEmpty
      , Apply [PL (length ps), WL]
      ]
genL env arg _ = throwM $ WrongArgument arg

export_command =
  [ ("assumption", assumption)
  , ("defer", defer)
  , ("implyR", implyR)
  , ("implyL", implyL)
  , ("genR", genR)
  , ("genL", genL)
  ]

---------------------------------------------

definition :: [Argument] -> Env -> IO Env
definition [ArgTyped i typ, ArgPreds [PredFml body]] = execStateT (declrunner decls) where
  decls =
    [ ConstD i typ
    , AxiomD (i ++ "_def") body
    ]
definition arg = \_ -> throwM $ WrongArguments arg

export_decl =
  [ ("definition", definition)
  ]


