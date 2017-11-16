module Claire.Laire.Syntax.Laire where

import Claire.Laire.Syntax.FOL
import Claire.Laire.Syntax.LK

type ThmIndex = String

data Laire = Laire [Decl]
  deriving (Show)

data Command
  = Apply [Rule]
  | Use ThmIndex [Maybe Predicate]
  | Inst Ident Predicate
  | NoApply Rule
  deriving (Show)

data Decl
  = ThmD ThmIndex Formula Proof
  | AxiomD ThmIndex Formula
  | ImportD String
  | PredD Formula
  | PrintProof
  deriving Show

data Proof
  = Proof [Command]
  deriving Show

