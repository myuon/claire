module Claire.Syntax.Claire where

import Claire.Syntax.FOL
import Claire.Syntax.LK

type ThmIndex = String

data Laire = Laire [Decl]
  deriving (Show)

type Pairs = [(Ident,Predicate)]

data Command
  = Apply [Rule]
  | Use ThmIndex Pairs
  | Inst Ident Predicate
  | NoApply Rule
  | NewCommand Ident Argument
  deriving (Show)

data Argument
  = ArgEmpty
  | ArgPreds [Predicate]
  | ArgTerms [Term]
  | ArgIdents [(Ident,Pairs)]
  deriving (Show)

data Decl
  = ThmD ThmIndex Formula Proof
  | AxiomD ThmIndex Formula
  | ImportD String
  | PrintProof
  | ConstD Ident Type
  | HsFile String
  | NewDecl Ident [Argument]
  deriving Show

data Proof
  = Proof [Command]
  deriving Show

