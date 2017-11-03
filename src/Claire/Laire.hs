module Claire.Laire
  ( Rule(..)
  , Judgement(..)

  , module Claire.Laire.Syntax
  , pFormula
  , pTerm
  ) where

import qualified Data.Sequence as S
import GHC.Exts (toList)

import Claire.Laire.Syntax
import Claire.Laire.Lexer
import Claire.Laire.Parser

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

