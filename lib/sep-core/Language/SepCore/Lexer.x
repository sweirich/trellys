{
module Language.SepCore.Lexer where

}

%wrapper "posn"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-

       $white+				;
       "--".*				;
       data       {\p s  -> TokenData p}
       Data       {\p s -> TokenData p}
       where      {\p s -> TokenWhere p}
       Where      {\p s -> TokenWhere p}
       type       {\p s -> TokenType p}
       Type       {\p s -> TokenType p}
       Formula    {\p s -> TokenFm p}
       formula    {\p s -> TokenFm p}
       Bottom     {\p s -> TokenBot p}
       bottom     {\p s -> TokenBot p}
       Pi         {\p s -> TokenPi p}
       pi         {\p s -> TokenPi p}
       Eq         {\p s -> TokenEq p}
       eq         {\p s -> TokenEq p}
       Forall     {\p s -> TokenForall p}
       forall     {\p s -> TokenForall p}
       "\"        {\p s -> TokenLamb p}
       abort      {\p s -> TokenAb p}
       Abort      {\p s -> TokenAb p}
       join       {\p s -> TokenJoin p}
       Join       {\p s -> TokenJoin p}
       contr      {\p s -> TokenContr p}
       Contr      {\p s -> TokenContr p}
       valax      {\p s -> TokenValax p}
       Valax      {\p s -> TokenValax p}
       "!"        {\p s -> TokenEx p}
       "("        {\p s -> TokenBL p}
       ")"        {\p s -> TokenBR p}
       "{"        {\p s -> TokenCBL p}
       "}"        {\p s -> TokenCBR p}
       "::"       {\p s -> TokenDC p}
       "+"        {\p s -> TokenPlus p}
       "-"        {\p s -> TokenMinus p}
       ":="       {\p s -> TokenDef p}
       ":"        {\p s -> TokenCL p}
       "."        {\p s -> TokenDot p}
       "|"        {\p s -> TokenBar p}
      $digit+				{ \p s -> TokenInt p (read s) }
      "$" $alpha [$alpha $digit \_ \']* {\p s -> TokenProofVar p s}
      $alpha [$alpha $digit \_ \']*     { \p s -> TokenTermVar p s }
      "@" $alpha [$alpha $digit \_ \']* {\p s -> TokenPredVar p s}
 
{


-- The token type:

data Token =

       TokenType AlexPosn

       | TokenDef AlexPosn        

       | TokenInt AlexPosn Integer

       | TokenFm AlexPosn

       | TokenForall AlexPosn
 
       | TokenProofVar AlexPosn String

       | TokenPredVar AlexPosn String

       | TokenTermVar AlexPosn String

       | TokenPi AlexPosn

       | TokenEq AlexPosn

       | TokenBot AlexPosn

       | TokenLamb AlexPosn

       | TokenJoin AlexPosn

       | TokenContr AlexPosn

       | TokenValax AlexPosn

       | TokenEx AlexPosn

       | TokenBL AlexPosn

       | TokenBR AlexPosn

       | TokenDC AlexPosn

       | TokenPlus AlexPosn

       | TokenMinus AlexPosn

       | TokenCL AlexPosn

       | TokenDot AlexPosn

       | TokenAb AlexPosn
 
       | TokenCBL AlexPosn

       | TokenCBR AlexPosn

       | TokenData AlexPosn

       | TokenWhere AlexPosn

       | TokenBar AlexPosn

  deriving (Show, Eq)

tokenPosn (TokenType p) = p

tokenPosn (TokenDef p) = p       

tokenPosn (TokenInt p i) = p

tokenPosn (TokenFm p) = p

tokenPosn (TokenForall p ) = p
 
tokenPosn (TokenProofVar p s) = p

tokenPosn (TokenPredVar p s) = p

tokenPosn (TokenTermVar p s) = p

tokenPosn (TokenPi p) = p

tokenPosn (TokenEq p) = p

tokenPosn (TokenBot p) = p

tokenPosn (TokenLamb p) = p 

tokenPosn (TokenJoin p) = p 

tokenPosn (TokenContr p) = p

tokenPosn (TokenValax p) = p

tokenPosn (TokenEx p) = p

tokenPosn (TokenBL p) = p

tokenPosn (TokenBR p) = p

tokenPosn (TokenDC p) = p

tokenPosn (TokenPlus p) = p

tokenPosn (TokenMinus p) = p

tokenPosn (TokenCL p) = p

tokenPosn (TokenDot p) = p

tokenPosn (TokenAb p) = p
 
tokenPosn (TokenCBL p) = p

tokenPosn (TokenCBR p) = p

tokenPosn (TokenData p) = p

tokenPosn (TokenWhere p) = p

tokenPosn (TokenBar p) = p




getLineNum :: AlexPosn -> Int
getLineNum (AlexPn offset lineNum colNum) = lineNum 

getColumnNum :: AlexPosn -> Int
getColumnNum (AlexPn offset lineNum colNum) = colNum


testlexer = do
  s <- getLine
  print (alexScanTokens s)
}