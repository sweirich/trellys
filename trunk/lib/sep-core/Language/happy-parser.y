{- The InterSep Parser -}
{
module Main where
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Subst(substR1)

}

%name InterSep-parser
%tokentype { Token }
%error { parseError }

%token 
       data
       proof      
       theorem
       type 
       term
       predicate
       kind
       data
       where      
       lambda
       pi
       forall
       formula
       name
        '+'
        '-' 
        ':'  
        "::"  
        ":=" 
        '('   
        ')'   
        '|'   
        '.'
%%
Datadecl : data Identifier Term where ConstrPair 
Theoremdecl : theorem Identifier "::" Predicate
Proofdef : proof Identifier ":=" Proof 
Typedecl : type Indentifier "::" Term
Progdef : term Indentifier ":=" Term
Predicatedecl : kind Indentifier "::" LogicalKind
Predicatedef : predicate Identifier ":=" Predicate



Identifier :
Term :
ConstrPair :
Proof : 




LogicalKind : formula int 
            | forall ArgClass '.' LogicalKind 

Predicate : name   
           
{
parseError :: [Token] -> a
parseError _ = error "Parse error"

data OttowaGrammar 
     = OttowaGrammar [String] [([String],String)]
     deriving Show

data Token 
      = TokenChar Char
      | TokenID String
      | TokenBNF
      | TokenMainSep
      | TokenPipe
      | TokenComma
      | TokenEq
      | TokenBang
      | TokenTilde
      | TokenTick
      | TokenAt
      | TokenHash
      | TokenDollar
      | TokenPercent
      | TokenCaret
      | TokenAnd
      | TokenStar
      | TokenLParen
      | TokenRParen
      | TokenDash
      | TokenUScore
      | TokenPlus
      | TokenLBrace
      | TokenRBrace
      | TokenLBracket
      | TokenRBracket
      | TokenFSlash
      | TokenBSlash
      | TokenColon
      | TokenSemiColon
      | TokenSQuote
      | TokenDQuote
      | TokenLt
      | TokenGt
      | TokenPeriod
      | TokenQuestion
      deriving Show

lexer :: String -> [Token]
lexer [] = []
lexer ('|':cs)  = TokenPipe : lexer cs
lexer (',':cs)  = TokenComma : lexer cs
lexer ('!':cs)  = TokenBang : lexer cs
lexer ('~':cs)  = TokenTilde : lexer cs
lexer ('`':cs)  = TokenTick : lexer cs
lexer ('@':cs)  = TokenAt : lexer cs
lexer ('#':cs)  = TokenHash : lexer cs
lexer ('$':cs)  = TokenDollar : lexer cs
lexer ('%':cs)  = TokenPercent : lexer cs
lexer ('^':cs)  = TokenCaret : lexer cs
lexer ('&':cs)  = TokenAnd : lexer cs
lexer ('*':cs)  = TokenStar : lexer cs
lexer ('(':cs)  = TokenLParen : lexer cs
lexer (')':cs)  = TokenRParen : lexer cs
lexer ('-':cs)  = TokenDash : lexer cs
lexer ('_':cs)  = TokenUScore : lexer cs
lexer ('+':cs)  = TokenPlus : lexer cs
lexer ('{':cs)  = TokenLBrace : lexer cs
lexer ('}':cs)  = TokenRBrace : lexer cs
lexer ('[':cs)  = TokenLBracket : lexer cs
lexer (']':cs)  = TokenRBracket : lexer cs
lexer ('\\':cs) = TokenFSlash : lexer cs
lexer ('/':cs)  = TokenBSlash : lexer cs
lexer (';':cs)  = TokenSemiColon : lexer cs
lexer ('\'':cs) = TokenSQuote : lexer cs
lexer ('"':cs)  = TokenDQuote : lexer cs
lexer ('<':cs)  = TokenLt : lexer cs
lexer ('>':cs)  = TokenGt : lexer cs
lexer ('.':cs)  = TokenPeriod : lexer cs
lexer ('?':cs)  = TokenQuestion : lexer cs
lexer (':':':':'=':rest) = TokenBNF     : lexer rest
lexer (':':':':rest)     = TokenMainSep : lexer rest
lexer (':':rest)         = TokenColon   : lexer rest
lexer ('=':rest)         = TokenEq      : lexer rest
lexer cs = case span isAlphaNumUn (dropWhile isSpace cs) of
             ("",cs')  -> lexer cs'
             (id,rest) -> TokenID id : lexer rest

isAlphaNumUn :: Char -> Bool
isAlphaNumUn c = isAlphaNum c || c == '_'

{- Our temp main loop. -}
main = getContents >>= print . ottowa_parse . lexer
--main = getContents >>= print . lexer
}
