{
module Claire.Parser.Parser where

import Claire.Syntax
import Claire.Parser.Lexer
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
  '}'       { TokenRBrace }
  '{'       { TokenLBrace }
  ']'       { TokenRBracket }
  '['       { TokenLBracket }
  'p['      { TokenPLBracket }
  't['      { TokenTLBracket }
  'i['      { TokenILBracket }
  'n['      { TokenNLBracket }
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
  print_proof  { TokenPrintProof }
  Hs_file   { TokenHsFile }
  constant  { TokenConstant }
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
  prop	    { TokenProp }
  newline   { TokenNewline }
  number    { TokenNumber $$ }
  strlit    { TokenStrLit $$ }
  ident     { TokenIdent $$ }
  tvar 	    { TokenTVar $$ }
  haskell   { TokenHaskellCode $$ }

%right '==>'
%left and or
%nonassoc '~'

%right '=>'

%%

Laire :: { Laire }
  : Decls  { Laire $1 }

Decls :: { [Decl] }
  : {- empty -}  { [] }
  | Decl Decls  { $1 : $2 }

Decl :: { Decl }
  : theorem ident ':' Formula Proof  { ThmD $2 $4 $5 }
  | axiom ident ':' Formula   	     { AxiomD $2 $4 }
  | import strlit   		     { ImportD $2 }
  | print_proof       	  	     { PrintProof }
  | constant ident ':' Type  	     { ConstD $2 $4 }
  | Hs_file strlit  		     { HsFile $2 }
  | ident '{' Arguments '}'	     { NewDecl $1 $3 }

Arguments :: { [Argument] }
  : {- empty -}			{ [] }
  | Argument Arguments		{ $1 : $2 }

Proof :: { Proof }
  : {- empty -}  { Proof [] }
  | proof Commands qed  { Proof $2 }

Commands :: { [Command] }
  : {- empty -}  { [] }
  | Command Commands  { $1 : $2 }

Command :: { Command }
  : apply Rule				{ Apply [$2] }
  | apply '(' Rules ')'			{ Apply $3 }
  | noapply Rule    			{ NoApply $2 }
  | use ident PairsExp			{ Use $2 $3 }
  | inst ident '[' Predicate ']'	{ Inst $2 $4 }
  | ident Argument  	     		{ NewCommand $1 $2 }

Argument :: { Argument }
  : {- empty -}				{ ArgEmpty }
  | 'p[' Predicates ']'  		{ ArgPreds $2 }
  | 'n[' ident ':' Type ']'  	 	{ ArgTyped $2 $4 }
  | 't[' Terms ']'  	 		{ ArgTerms $2 }
  | 'i[' IdentPairs ']'  		{ ArgIdents $2 }

Predicates :: { [Predicate] }
  : {- empty -}				{ [] }
  | Predicate				{ [$1] }
  | Predicate ',' Predicates		{ $1 : $3 }

Predicate :: { Predicate }
  : ident '=>' Predicate		{ PredFun [$1] $3 }
  | '(' Idents ')' '=>' Predicate	{ PredFun $2 $5 }
  | Formula  { PredFml $1 }

Idents :: { [Ident] }
  : ident				{ [$1] }
  | ident ',' Idents			{ $1 : $3 }

IdentPairs :: { [(Ident,Pairs)] }
  : ident PairsExp			{ [($1,$2)] }
  | ident PairsExp ',' IdentPairs	{ ($1,$2) : $4 }

PairsExp :: { Pairs }
  : {- empty -}				{ [] }
  | '{' Pairs '}'			{ $2 }

Pairs :: { Pairs }
  : ident ':' Predicate			{ [($1,$3)] }
  | ident ':' Predicate ',' Pairs	{ ($1,$3) : $5 }

Rules :: { [Rule] }
  : Rule  { [$1] }
  | Rule ',' Rules  { $1 : $3 }

Rule :: { Rule }
  : I				{ I }
  | Cut '[' Formula ']'  	{ Cut $3 }
  | AndL1   	    		{ AndL1 }
  | AndL2 			{ AndL2 }
  | AndR			{ AndR }
  | OrL				{ OrL }
  | OrR1			{ OrR1 }
  | OrR2			{ OrR2 }
  | ImpL			{ ImpL }
  | ImpR			{ ImpR }
  | BottomL			{ BottomL }
  | TopR			{ TopR }
  | ForallL '[' Term ']'  	{ ForallL $3 }
  | ForallR ident    		{ ForallR $2 }
  | ExistL ident  		{ ExistL $2 }
  | ExistR '[' Term ']'  	{ ExistR $3 }
  | WL         	    		{ WL }
  | WR				{ WR }
  | CL				{ CL }
  | CR				{ CR }
  | PL number			{ PL $2 }
  | PR number			{ PR $2 }

Formula :: { Formula }
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

Terms :: { [Term] }
  : {- empty -}  { [] }
  | Term  { [$1] }
  | Term ',' Terms  { $1 : $3 }

Term :: { Term }
  : Term '(' Terms ')'  	{ App $1 $3 }
  | ident '=>' Term  		{ Abs [$1] $3 }
  | '(' Idents ')' '=>' Term  	{ Abs $2 $5 }
  | '(' Term ')'    		{ $2 }
  | ident			{ Var $1 }

Type :: { Type }
  : prop			{ Prop }
  | tvar			{ VarT $1 }
  | ident 			{ ConT $1 [] }
  | ident '(' Types ')'		{ ConT $1 $3 }
  | Type '=>' Type  		{ ArrT $1 $3 }
  | '(' Type ')'  		{ $2 }

Types :: { [Type] }
  : Type  { [$1] }
  | Type ',' Types { $1 : $3 }

{
happyError s = error $ show s
}

