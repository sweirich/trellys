{
module Language.SepCore.Lexer 
 (Token(..)) where

}

%wrapper "basic"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-

       $white+				;
       "--".*				;
       data       {\s -> TokenData}
       Data       {\s -> TokenData}
       where      {\s -> TokenWhere}
       Where      {\s -> TokenWhere}
       ProofVar   {TokenProofVar $$}
       PredVar    {TokenPredVar $$}
       TermVar    {TokenTermVar $$}
       int        {TokenInt $$}
       type       {\s -> TokenType}
       Type       {\s -> TokenType}
       Formula    {\s -> TokenFm}
       formula    {\s -> TokenFm}
       Bottom     {\s -> TokenBot}
       bottom     {\s -> TokenBot}
       Pi         {\s -> TokenPi}
       pi         {\s -> TokenPi}
       Eq         {\s -> TokenEq}
       eq         {\s -> TokenEq}
       Forall     {\s -> TokenForall}
       forall     {\s -> TokenForall}
       '\\'       {\s -> TokenLamb}
       abort      {\s -> TokenAb}
       Abort      {\s -> TokenAb}
       join       {\s -> TokenJoin}
       Join       {\s -> TokenJoin}
       contr      {\s -> TokenContr}
       Contr      {\s -> TokenContr}
       valax      {\s -> TokenValax}
       Valax      {\s -> TokenValax}
       '!'        {\s -> TokenEx}
       '('        {\s -> TokenBL}
       ')'        {\s -> TokenBR}
       '{'        {\s -> TokenCBL}
       '}'        {\s -> TokenCBR}
       "::"       {\s -> TokenDC}
       '+'        {\s -> TokenPlus}
       '-'        {\s -> TokenMinus}
       ":="       {\s -> TokenDef}
       ':'        {\s -> TokenCL}
       '.'        {\s -> TokenDot}
       '|'        {\s -> TokenBar}
  
      $digit+				{ \s -> Int (read s) }
      [\=\+\-\*\/\(\)]			{ \s -> Sym (head s) }
      $alpha [$alpha $digit \_ \']*		{ \s -> Var s }

{
-- Each action has type :: String -> Token

-- The token type:

data Token =

       TokenType

       | TokenDef        

       | TokenId String

       | TokenInt Integer

       | TokenFm

       | TokenForall
 
       | TokenProofVar String

       | TokenPredVar String

       | TokenTermVar String

       | TokenPi

       | TokenEq

       | TokenBot

       | TokenLamb

       | TokenJoin

       | TokenContr

       | TokenValax

       | TokenEx

       | TokenBL

       | TokenBR

       | TokenDC

       | TokenPlus

       | TokenMinus

       | TokenCL

       | TokenDot

       | TokenAb
 
       | TokenCBL

       | TokenCBR

       | TokenData

       | TokenWhere

       | TokenBar

  deriving (Show, Eq)

testlexer = do
  s <- getLine
  print (alexScanTokens s)
}