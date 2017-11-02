{
module Claire.FOL.Lexer where

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
  "\\/"    { \s -> TokenOr }
  "/\\"    { \s -> TokenAnd }
  "."      { \s -> TokenDot }
  ","      { \s -> TokenComma }
  "("      { \s -> TokenLParen }
  ")"      { \s -> TokenRParen }
  "~"      { \s -> TokenTilda }
  $alpha [$alpha $digit \_ \']*      { TokenSym }

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
  | TokenSym String
  | TokenComma
  | TokenLParen
  | TokenRParen
  | TokenTilda
  deriving (Eq, Show)
}

