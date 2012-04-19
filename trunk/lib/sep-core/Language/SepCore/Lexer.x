
{
module Language.SepCore.Lexer where

}

%wrapper "monad"

$digit = 0-9		
$alpha = [a-zA-Z]	

@num = $digit+
@proofVar = "$" $alpha [$alpha $digit \_ \']*
@termVar = $alpha [$alpha $digit \_ \']*
@predVar = "@" $alpha [$alpha $digit \_ \']*
@comments =  "--".* 

@reservedWords = data | Data | where | Where | type | Type | Formula | formula
                | Bottom | bottom | pi | Pi | Eq | eq | Forall | forall | abort | Abort
                | join | Join | contr | Contr | valax | Valax

@reservedSymbols = \\ | "!" | "(" | ")" | "{" | "}" | "::" | ":" | "+" | "-" | ":="
                  | "." | "|"
tokens :-
-- Notice: the order of the following productions actually matters. Becase there is
-- a potential overlapping between termvar and reservedwords. So we need to scan reservedwords 
-- first, and then scan other variables.

       $white+				;
       @comments                        ;
       @num                             {lexNum}
       @reservedWords                   {lexReservedW}
       @proofVar                        {lexProofVar}
       @termVar                         {lexTermVar}
       @predVar                         {lexPredVar}
       @reservedSymbols                 {lexReservedS}
                    

 
{


-- The token type:

data Token =

       TokenType 

       | TokenDef

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

       | TokenEOF
  deriving (Show, Eq)

data Lexeme = L AlexPosn Token String

mkL :: Token -> AlexInput -> Int -> Alex Lexeme
mkL t (p,_,str) len = return (L p t (take len str))

lexNum :: AlexInput -> Int -> Alex Lexeme
lexNum a@(_,_,input) len = mkL (TokenInt (read (take len input))) a len

lexProofVar :: AlexInput -> Int -> Alex Lexeme
lexProofVar a@(_,_,input) len = mkL (TokenProofVar (take len input)) a len

lexTermVar :: AlexInput -> Int -> Alex Lexeme
lexTermVar a@(_,_,input) len = mkL (TokenTermVar (take len input)) a len

lexPredVar :: AlexInput -> Int -> Alex Lexeme
lexPredVar a@(_,_,input) len = mkL (TokenPredVar (take len input)) a len

lexReservedW :: AlexInput -> Int -> Alex Lexeme
lexReservedW a@(_,_,input) len = case take len input of
                                    "data" -> mkL TokenData a len 
                                    "Data" -> mkL TokenData a len
                                    "where" -> mkL TokenWhere a len
                                    "Where" -> mkL TokenWhere a len
                                    "Type" -> mkL TokenType a len
                                    "type" -> mkL TokenType a len
                                    "formula" -> mkL TokenFm a len
                                    "Formula" -> mkL TokenFm a len
                                    "Bottom" -> mkL TokenBot a len
                                    "bottom" -> mkL TokenBot a len
                                    "pi" -> mkL TokenPi a len
                                    "Pi" -> mkL TokenPi a len
                                    "Eq" -> mkL TokenEq a len
                                    "eq" -> mkL TokenEq a len
                                    "forall" -> mkL TokenForall a len
                                    "Forall" -> mkL TokenForall a len
                                    "abort" -> mkL TokenAb a len
                                    "Abort" -> mkL TokenAb a len
                                    "Join" -> mkL TokenJoin a len
                                    "join" -> mkL TokenJoin a len
                                    "Contr" -> mkL TokenContr a len
                                    "contr" -> mkL TokenContr a len
                                    "valax" -> mkL TokenValax a len
                                    "Valax" -> mkL TokenValax a len
-- @reservedSymbols = "\\" | "!" | "(" | ")" | "{" | "}" | "::" | ":" | "+" | "-" | ":="
--                  | "." | "|"

lexReservedS :: AlexInput -> Int -> Alex Lexeme
lexReservedS a@(_,_,input) len = case take len input of
                                    "\\" -> mkL TokenLamb a len 
                                    "!" -> mkL TokenEx a len
                                    "(" -> mkL TokenBL a len
                                    ")" -> mkL TokenBR a len
                                    "{" -> mkL TokenCBL a len
                                    "}" -> mkL TokenCBR a len
                                    "::" -> mkL TokenDC a len
                                    ":" -> mkL TokenCL a len
                                    "-" -> mkL TokenMinus a len
                                    "+" -> mkL TokenPlus a len
                                    ":=" -> mkL TokenDef a len
                                    "." -> mkL TokenDot a len
                                    "|" -> mkL TokenBar a len


getLineNum :: AlexPosn -> Int
getLineNum (AlexPn offset lineNum colNum) = lineNum 

getColumnNum :: AlexPosn -> Int
getColumnNum (AlexPn offset lineNum colNum) = colNum

alexMonadScan2 = do
  inp <- alexGetInput
  sc <- alexGetStartCode
  case alexScan inp sc of
    AlexEOF -> alexEOF
    AlexError inp'@(p,_,s) -> alexError $ "Lexical error at line: "++ show (getLineNum p) ++ ", column: " ++ show (getColumnNum p) ++ "."
    AlexSkip  inp' len -> do
        alexSetInput inp'
        alexMonadScan2
    AlexToken inp' len action -> do
        alexSetInput inp'
        action inp len

alexEOF = return (L undefined TokenEOF "")

{-
-- some unusable test code.

scanner str = runAlex str $ do
  let loop t = do tok@(L _ cl _) <- alexMonadScan2; 
		  if cl == TokenEOF
			then return t
			else do loop $! (t ++ [cl])
  loop []

test = do
  s <- getLine
  print (scanner s)

-}


}




