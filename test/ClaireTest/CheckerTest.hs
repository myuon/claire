module ClaireTest.CheckerTest where

import Test.Tasty.HUnit
import Claire

test_checker =
  [ testCase "prove: a -> a" $ checker' [ImpI, Init "0"] (Const "a" :->: Const "a") @?= Right []
  , testCase "prove: ~ (p /\\ q) -> ~p \\/ ~q" $ checker'
    [ImpI, Abs, ImpE (Const "p" :/\: Const "q"), Init "0",
     AndI,
      Abs, ImpE (Neg (Const "p") :\/: Neg (Const "q")), Init "1", OrI1, Init "2",
      Abs, ImpE (Neg (Const "p") :\/: Neg (Const "q")), Init "1", OrI2, Init "2"
    ] (Neg (Const "p" :/\: Const "q") :->: (Neg (Const "p") :\/: Neg (Const "q"))) @?= Right []
  ]

