{
module Claire.Laire.Parser where

import Claire.Laire.Syntax
import Claire.Laire.Lexer
}

%name laireparser
%name declparser Decl
%name comparser Command
%name folparser Formula
%name termparser Term

%tokentype { Token }

%token
  forall    { TokenForall }
  exist     { TokenExist }
  top       { TokenTop }
  bottom    { TokenBottom }
  '==>'     { TokenArrow }
  '=>'      { TokenFun }
  and       { TokenAnd }
  or        { TokenOr }
  '.'       { TokenDot }
  ','       { TokenComma }
  ')'       { TokenRParen }
  '('       { TokenLParen }
  ']'       { TokenRBracket }
  '['       { TokenLBracket }
  '~'       { TokenTilda }
  ':'       { TokenColon }
  ';'       { TokenSemicolon }
  '|'       { TokenHBar }
  '='	    { TokenEqual }
  '_'	    { TokenUnderscore }
  theorem   { TokenTheorem }
  axiom     { TokenAxiom }
  proof     { TokenProof }
  qed       { TokenQed }
  import    { TokenImport }
  predicate { TokenPredicate }
  print_proof  { TokenPrintProof }
  term	    { TokenTerm }
  apply     { TokenApply }
  noapply   { TokenNoApply }
  use       { TokenUse }
  inst	    { TokenInst }
  I         { TokenI }
  Cut       { TokenCut }
  AndL1     { TokenAndL1 }
  AndL2     { TokenAndL2 }
  AndR      { TokenAndR }
  OrL       { TokenOrL }
  OrR1      { TokenOrR1 }
  OrR2      { TokenOrR2 }
  ImpL      { TokenImpL }
  ImpR      { TokenImpR }
  BottomL   { TokenBottomL }
  TopR      { TokenTopR }
  ForallL   { TokenForallL }
  ForallR   { TokenForallR }
  ExistL    { TokenExistL }
  ExistR    { TokenExistR }
  WL        { TokenWL }
  WR        { TokenWR }
  CL        { TokenCL }
  CR        { TokenCR }
  PL        { TokenPL }
  PR        { TokenPR }
  newline   { TokenNewline }
  number    { TokenNumber $$ }
  strlit    { TokenStrLit $$ }
  ident     { TokenIdent $$ }
  haskell   { TokenHaskellCode $$ }

%right '==>'
%left and or
%nonassoc '~'

%right '=>'

%%

Laire
  : Decls  { Laire $1 }

Decls
  : {- empty -}  { [] }
  | Decl Decls  { $1 : $2 }

Decl
  : theorem ident ':' Formula Proof  { ThmD $2 $4 $5 }
  | axiom ident ':' Formula  { AxiomD $2 $4 }
  | import strlit  { ImportD $2 }
  | predicate Formula  { PredD $2 }
  | print_proof  { PrintProof }
  | term Term  { TermD $2 }

Proof
  : {- empty -}  { Proof [] }
  | proof Commands qed  { Proof $2 }

Commands
  : {- empty -}  { [] }
  | Command Commands  { $1 : $2 }

Command
  : apply Rule  { Apply [$2] }
  | apply '(' Rules ')'  { Apply $3 }
  | noapply Rule  { NoApply $2 }
  | use ident  { Use $2 }
  | inst ident '[' Predicate ']'  { Inst $2 $4 }

Predicates
  : {- empty -}  { [] }
  | Predicate  { [Just $1] }
  | '_'  { [Nothing] }
  | Predicate ',' Predicates  { Just $1 : $3 }
  | '_' ',' Predicates  { Nothing : $3 }

Predicate
  : Arguments '=>' Predicate  { PredFun $1 $3 }
  | Formula  { PredFml $1 }

Arguments
  : ident  { [$1] }
  | '(' Idents ')'  { $2 }

Idents
  : ident  { [$1] }
  | ident ',' Idents { $1 : $3 }

Rules
  : Rule  { [$1] }
  | Rule ',' Rules  { $1 : $3 }

Rule
  : I  { I }
  | Cut '[' Formula ']'  { Cut $3 }
  | AndL1  { AndL1 }
  | AndL2  { AndL2 }
  | AndR  { AndR }
  | OrL  { OrL }
  | OrR1  { OrR1 }
  | OrR2  { OrR2 }
  | ImpL  { ImpL }
  | ImpR  { ImpR }
  | BottomL  { BottomL }
  | TopR  { TopR }
  | ForallL '[' Term ']'  { ForallL $3 }
  | ForallR ident  { ForallR $2 }
  | ExistL ident  { ExistL $2 }
  | ExistR '[' Term ']'  { ExistR $3 }
  | WL  { WL }
  | WR  { WR }
  | CL  { CL }
  | CR  { CR }
  | PL number  { PL $2 }
  | PR number  { PR $2 }

Formula
  : Formula '==>' Formula     { $1 :==>: $3 }
  | forall ident '.' Formula  { Forall $2 $4 }
  | exist ident '.' Formula   { Exist $2 $4 }
  | Formula or Formula        { $1 :\/: $3 }
  | Formula and Formula       { $1 :/\: $3 }
  | '~' Formula               { Neg $2 }
  | top                       { Top }
  | bottom                    { Bottom }
  | '(' Formula ')'           { $2 }
  | ident '(' Terms ')'       { Pred $1 $3 }
  | ident                     { Pred $1 [] }

Terms
  : {- empty -}  { [] }
  | Term  { [$1] }
  | Term ',' Terms  { $1 : $3 }

Term
  : ident  { Var $1 }
  | ident '(' Terms ')'  { Func $1 $3 }

{
happyError s = error $ show s
}

