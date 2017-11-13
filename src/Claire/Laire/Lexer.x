{
module Claire.Laire.Lexer where

}

%wrapper "basic"

$digit = [0-9]
$alpha = [a-zA-Z]

tokens :-
  $white+  ;
  "#".*    ;
  forall   { \s -> TokenForall }
  exist    { \s -> TokenExist }
  top      { \s -> TokenTop }
  bottom   { \s -> TokenBottom }
  "->"     { \s -> TokenArrow }
  "\/"     { \s -> TokenOr }
  "/\"     { \s -> TokenAnd }
  "."      { \s -> TokenDot }
  ","      { \s -> TokenComma }
  "("      { \s -> TokenLParen }
  ")"      { \s -> TokenRParen }
  "["      { \s -> TokenLBracket }
  "]"      { \s -> TokenRBracket }
  "~"      { \s -> TokenTilda }
  [\n]     { \s -> TokenNewline }
  ":"      { \s -> TokenColon }
  ";"      { \s -> TokenSemicolon }
  "|"	   { \s -> TokenHBar }
  "="	   { \s -> TokenEqual }
  theorem  { \s -> TokenTheorem }
  proof    { \s -> TokenProof }
  qed      { \s -> TokenQed }
  axiom    { \s -> TokenAxiom }
  datatype { \s -> TokenDatatype }
  import   { \s -> TokenImport }
  apply    { \s -> TokenApply }
  use      { \s -> TokenUse }
  Cut      { \s -> TokenCut }
  I        { \s -> TokenI }
  Cut      { \s -> TokenCut }
  AndL1    { \s -> TokenAndL1 }
  AndL2    { \s -> TokenAndL2 }
  AndR     { \s -> TokenAndR }
  OrL      { \s -> TokenOrL }
  OrR1     { \s -> TokenOrR1 }
  OrR2     { \s -> TokenOrR2 }
  ImpL     { \s -> TokenImpL }
  ImpR     { \s -> TokenImpR }
  BottomL  { \s -> TokenBottomL }
  TopR     { \s -> TokenTopR }
  ForallL  { \s -> TokenForallL }
  ForallR  { \s -> TokenForallR }
  ExistL   { \s -> TokenExistL }
  ExistR   { \s -> TokenExistR }
  WL       { \s -> TokenWL }
  WR       { \s -> TokenWR }
  CL       { \s -> TokenCL }
  CR       { \s -> TokenCR }
  PL       { \s -> TokenPL }
  PR       { \s -> TokenPR }
  $digit+  { \s -> TokenNumber (read s) }
  \"[^\\\"]*\"  { \s -> TokenStrLit (tail $ init s) }
  $alpha [$alpha $digit \_ \']*      { TokenIdent }

{
data Token
  = TokenForall
  | TokenExist
  | TokenTop
  | TokenBottom
  | TokenArrow
  | TokenOr
  | TokenAnd
  | TokenDot
  | TokenComma
  | TokenLParen
  | TokenRParen
  | TokenLBracket
  | TokenRBracket
  | TokenTilda
  | TokenNewline
  | TokenColon
  | TokenSemicolon
  | TokenHBar
  | TokenEqual
  | TokenTheorem
  | TokenProof
  | TokenQed
  | TokenAxiom
  | TokenDatatype
  | TokenImport
  | TokenApply
  | TokenUse
  | TokenI
  | TokenCut
  | TokenAndL1
  | TokenAndL2
  | TokenAndR
  | TokenOrL
  | TokenOrR1
  | TokenOrR2
  | TokenImpL
  | TokenImpR
  | TokenBottomL
  | TokenTopR
  | TokenForallL
  | TokenForallR
  | TokenExistL
  | TokenExistR
  | TokenWL
  | TokenWR
  | TokenCL
  | TokenCR
  | TokenPL
  | TokenPR
  | TokenNumber Int
  | TokenIdent String
  | TokenStrLit String
  deriving (Eq, Show)
}

