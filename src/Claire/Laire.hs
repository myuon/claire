module Claire.Laire
  ( Rule(..)
  , Judgement(..)

  , module Claire.Laire.Syntax
  , pLaire
  , pFormula
  , pTerm
  ) where

import Claire.Laire.Syntax
import Claire.Laire.Lexer
import Claire.Laire.Parser

pLaire :: String -> Laire
pLaire = laireparser . alexScanTokens

pFormula :: String -> Formula
pFormula = folparser . alexScanTokens

pTerm :: String -> Term
pTerm = termparser . alexScanTokens


