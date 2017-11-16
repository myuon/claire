module ClaireTest.CheckerTest where

import Test.Tasty.HUnit
import Claire

test_checker =
  [ testCase "prove: a -> a" $ judge defEnv [ImpR, I] (newGoal $ Const "a" :==>: Const "a") @?= Right []
  , testCase "prove: ~ (p /\\ q) -> ~p \\/ ~q" $ judge defEnv
    [ ImpR
    , ImpL
      , AndR
        , PR 1, OrR1, ImpR, WR, I
        , PR 1, OrR2, ImpR, WR, I
      , BottomL
    ] (newGoal $ Neg (Const "p" :/\: Const "q") :==>: (Neg (Const "p") :\/: Neg (Const "q"))) @?= Right []
  ]

