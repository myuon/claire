module ClaireTest.CheckerTest where

import Test.Tasty.HUnit
import Claire

test_checker =
  [ testCase "prove: a -> a" $ checker' [NegR, CL, AndL2, NegL, AndL1, NegL, NegR, I] (FmlTerm (Var "a") :-->: FmlTerm (Var "a")) @?= Right []
  ]

