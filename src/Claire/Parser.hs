module Claire.Parser
  ( module Claire.Syntax
  , pLaire
  , pDecl
  , pCommand
  , pFormula
  , pTerm

  ) where

import Claire.Syntax
import Claire.Parser.Lexer
import Claire.Parser.Parser

pLaire :: String -> Laire
pLaire = laireparser . alexScanTokens

pDecl :: String -> Decl
pDecl = declparser . alexScanTokens

pCommand :: String -> Command
pCommand = comparser . alexScanTokens

pFormula :: String -> Formula
pFormula = folparser . alexScanTokens

pTerm :: String -> Term
pTerm = termparser . alexScanTokens

