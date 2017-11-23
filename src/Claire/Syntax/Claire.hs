module Claire.Syntax.Claire where

import Claire.Syntax.FOL
import Claire.Syntax.LK

type ThmIndex = String

data Laire = Laire [Decl]
  deriving (Show)

data Command
  = Apply [Rule]
  | Use ThmIndex
  | Inst Ident Predicate
  | NoApply Rule
  | NewCommand Ident
  deriving (Show)

data Decl
  = ThmD ThmIndex Formula Proof
  | AxiomD ThmIndex Formula
  | ImportD String
  | PredD Formula Type
  | PrintProof
  | TermD Term Type
  | HsFile String
  deriving Show

data Proof
  = Proof [Command]
  deriving Show

