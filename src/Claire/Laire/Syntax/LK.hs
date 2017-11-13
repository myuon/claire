module Claire.Laire.Syntax.LK where

import Data.Sequence as S
import Claire.Laire.Syntax.FOL
import GHC.Exts (toList)

type AssmIndex = String

data Rule
  = I | Cut Formula
  | AndL1 | AndL2 | AndR
  | OrL | OrR1 | OrR2
  | ImpL | ImpR
  | BottomL | TopR
  | ForallL Term | ForallR Ident
  | ExistL Ident | ExistR Term
  | WL | WR
  | CL | CR
  | PL Int | PR Int
  deriving (Eq, Show)

data Judgement = Judgement (S.Seq Formula) (S.Seq Formula) deriving (Eq)

instance Show Judgement where
  show (Judgement assms prop) = show (toList assms) ++ " |- " ++ show prop


