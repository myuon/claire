module ClaireTest.FOLTest where

import Test.Tasty.HUnit
import Claire

test_pFormula =
  [ testCase "Var a" $ pFormula "a" @?= Const "a"
  , testCase "a /\\ b" $ pFormula "a /\\ b" @?= Const "a" :/\: Const "b"
  , testCase "Top" $ pFormula "Top" @?= Top
  , testCase "Bottom" $ pFormula "Bottom" @?= Bottom
  , testCase "p ==> q" $ pFormula "p ==> q" @?= Const "p" :==>: Const "q"
  , testCase "p ==> q /\\ q' ==> r" $ pFormula "p ==> (q /\\ q' ==> r)" @?= Const "p" :==>: ((Const "q" :/\: Const "q'") :==>: Const "r")
  , testCase "p /\\ q /\\ r" $ pFormula "p /\\ q /\\ r" @?= (Const "p" :/\: Const "q") :/\: Const "r"
  , testCase "~p /\\ ~q" $ pFormula "~p /\\ ~ q" @?= Neg (Const "p") :/\: Neg (Const "q")
  ]

