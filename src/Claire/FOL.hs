module Claire.FOL
  ( Rule(..)
  , Judgement(..)

  , module Claire.FOL.Syntax
  , pFormula
  , pTerm
  , addAssm
  ) where

import qualified Data.Map as M
import GHC.Exts (toList)

import Claire.FOL.Syntax
import Claire.FOL.Lexer
import Claire.FOL.Parser

pFormula :: String -> Formula
pFormula = folparser . alexScanTokens

pTerm :: String -> Term
pTerm = termparser . alexScanTokens

type AssmIndex = String

-- rules for natural deduction
data Rule
  = Init AssmIndex | Abs
  | TopI | BottomE
  | AndI | AndE1 Formula | AndE2 Formula
  | OrI1 | OrI2 | OrE Formula Formula
  | ImpI | ImpE Formula
  | ForallI | ForallE Term VSymbol
  | ExistI Term | ExistE Formula
  deriving (Eq, Show)

data Judgement = Judgement (M.Map AssmIndex Formula) Formula deriving (Eq)

addAssm :: Formula -> M.Map AssmIndex Formula -> M.Map AssmIndex Formula
addAssm fml assms = M.insert (show $ M.size assms) fml assms

instance Show Judgement where
  show (Judgement assms prop) = show (toList assms) ++ " |- " ++ show prop

