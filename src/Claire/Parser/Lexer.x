{
module Claire.Parser.Lexer where

}

%wrapper "basic"

$digit = [0-9]
$alpha = [a-zA-Z]

tokens :-
  $white+   ;
  "#".*     ;
  Forall    { \s -> TokenForall }
  Exist     { \s -> TokenExist }
  Top       { \s -> TokenTop }
  Bottom    { \s -> TokenBottom }
  "==>"     { \s -> TokenArrow }
  "=>"	    { \s -> TokenFun }
  "\/"      { \s -> TokenOr }
  "/\"      { \s -> TokenAnd }
  "."       { \s -> TokenDot }
  ","       { \s -> TokenComma }
  "("       { \s -> TokenLParen }
  ")"       { \s -> TokenRParen }
  "{"       { \s -> TokenLBrace }
  "}"       { \s -> TokenRBrace }
  "["       { \s -> TokenLBracket }
  "p["      { \s -> TokenPLBracket }
  "t["      { \s -> TokenTLBracket }
  "i["      { \s -> TokenILBracket }
  "]"       { \s -> TokenRBracket }
  "~"       { \s -> TokenTilda }
  [\n]      { \s -> TokenNewline }
  ":"       { \s -> TokenColon }
  ";"       { \s -> TokenSemicolon }
  "|"	    { \s -> TokenHBar }
  "="	    { \s -> TokenEqual }
  "_"	    { \s -> TokenUnderscore }
  theorem   { \s -> TokenTheorem }
  proof     { \s -> TokenProof }
  qed       { \s -> TokenQed }
  axiom     { \s -> TokenAxiom }
  import    { \s -> TokenImport }
  predicate { \s -> TokenPredicate }
  term	    { \s -> TokenTerm }
  "print_proof"  { \s -> TokenPrintProof }
  "Hs_file" { \s -> TokenHsFile }
  apply     { \s -> TokenApply }
  noapply   { \s -> TokenNoApply }
  use       { \s -> TokenUse }
  inst	    { \s -> TokenInst }
  Cut       { \s -> TokenCut }
  I         { \s -> TokenI }
  Cut       { \s -> TokenCut }
  AndL1     { \s -> TokenAndL1 }
  AndL2     { \s -> TokenAndL2 }
  AndR      { \s -> TokenAndR }
  OrL       { \s -> TokenOrL }
  OrR1      { \s -> TokenOrR1 }
  OrR2      { \s -> TokenOrR2 }
  ImpL      { \s -> TokenImpL }
  ImpR      { \s -> TokenImpR }
  BottomL   { \s -> TokenBottomL }
  TopR      { \s -> TokenTopR }
  ForallL   { \s -> TokenForallL }
  ForallR   { \s -> TokenForallR }
  ExistL    { \s -> TokenExistL }
  ExistR    { \s -> TokenExistR }
  WL        { \s -> TokenWL }
  WR        { \s -> TokenWR }
  CL        { \s -> TokenCL }
  CR        { \s -> TokenCR }
  PL        { \s -> TokenPL }
  PR        { \s -> TokenPR }
  prop	    { \s -> TokenProp }
  $digit+   { \s -> TokenNumber (read s) }
  \"[^\\\"]*\"  { \s -> TokenStrLit (tail $ init s) }
  ```[^```]*```  { \s -> TokenHaskellCode s }
  \' $alpha [$alpha $digit \_]*  { TokenTVar }
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
  | TokenLBrace
  | TokenRBrace
  | TokenLBracket
  | TokenPLBracket
  | TokenTLBracket
  | TokenILBracket
  | TokenRBracket
  | TokenTilda
  | TokenNewline
  | TokenColon
  | TokenSemicolon
  | TokenHBar
  | TokenEqual
  | TokenUnderscore
  | TokenFun
  | TokenTheorem
  | TokenProof
  | TokenQed
  | TokenAxiom
  | TokenPredicate
  | TokenPrintProof
  | TokenHsFile
  | TokenTerm
  | TokenImport
  | TokenApply
  | TokenNoApply
  | TokenUse
  | TokenInst
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
  | TokenProp
  | TokenNumber Int
  | TokenIdent String
  | TokenStrLit String
  | TokenHaskellCode String
  | TokenTVar String
  deriving (Eq, Show)
}

