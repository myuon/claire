module Claire.Syntax.LK where

import Claire.Syntax.FOL

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

data Judgement = Judgement [Formula] [Formula] deriving (Eq)

instance Show Judgement where
  show (Judgement assms prop) = show (reverse assms) ++ " |- " ++ show prop

formulize :: Judgement -> Formula
formulize (Judgement assms props) = foldl (:/\:) Top assms :==>: foldl (:\/:) Bottom props

