module Claire.FOL
  ( Rule(..)
  , Judgement(..)

  , module Claire.FOL.Syntax
  , pFormula
  , pTerm
  ) where

import qualified Data.Sequence as S
import GHC.Exts (toList)

import Claire.FOL.Syntax
import Claire.FOL.Lexer
import Claire.FOL.Parser

pFormula :: String -> Formula
pFormula = folparser . alexScanTokens

pTerm :: String -> Term
pTerm = termparser . alexScanTokens

type AssmIndex = String

-- rules for LK
data Rule
  = I | Cut Formula
  | AndL1 | AndL2 | AndR
  | OrL | OrR1 | OrR2
  | ImpL | ImpR
  | BottomL | TopR
  | ForallL Term | ForallR VSymbol
  | ExistL VSymbol | ExistR Term
  | WL | WR
  | CL | CR
  | PL Int | PR Int
  deriving (Eq, Show)

data Judgement = Judgement (S.Seq Formula) (S.Seq Formula) deriving (Eq)

instance Show Judgement where
  show (Judgement assms prop) = show (toList assms) ++ " |- " ++ show prop

