module ClaireTest.FOLTest where

import Control.Lens
import Test.Tasty.HUnit
import Claire

test_pFormula =
  [ testCase "Var a" $ pFormula "a" ^?! _Success @?= FmlTerm (Var "a")
  , testCase "a /\\ b" $ pFormula "a /\\ b" ^?! _Success @?= FmlTerm (Var "a") :/\: FmlTerm (Var "b")
  , testCase "~ a" $ pFormula "~ a" ^?! _Success @?= Neg (FmlTerm (Var "a"))
  ]

