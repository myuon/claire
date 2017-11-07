module Claire.Laire.Syntax.Laire where

import Claire.Laire.Syntax.FOL
import Claire.Laire.Syntax.LK

type ThmIndex = String

data Laire = Laire [Decl]
  deriving (Show)

data Command
  = Apply [Rule]
  | Use ThmIndex
  deriving (Show)

data Decl
  = ThmD ThmIndex Formula
  | AxiomD ThmIndex Formula
  | PrfD Proof
  deriving Show

data Proof
  = Proof [Command]
  deriving Show

