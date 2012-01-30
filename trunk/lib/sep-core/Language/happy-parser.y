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
       formula
       string
       int
       proof      
       theorem
       type 
       term
       predicate
       kind
       data
       where      
       lambda
       Lambda
       Pi
       forall
       rec
       let
       in
       conv
       by
       at
       case
       of
       cast
       abort
       inl 
       inr
       with
       join
       predconv
       valax
       ord
       contr 
       ind 
       contraval




        '='
        '+'
        '-' 
        ':'  
        "::"  
        ":=" 
        '('   
        ')'   
        '|'   
        '.'
        '['
        ']'
        ','
        "=>"
        '!'
%%

{-Top level definitions and declarations -}

Datadecl : data Identifier Term where ConstrPair 

Theoremdecl : theorem Identifier "::" Predicate

Proofdef : proof Identifier ":=" Proof 

Typedecl : type Identifier "::" Term

Progdef : term Identifier ":=" Term

LogicalKinddecl : kind Identifier "::" LogicalKind

Predicatedef : predicate Identifier ":=" Predicate

{-Non Top level definitions-}

Identifier : string

Dataconstr : string

ArgClass : Term 
         | Predicate
         | LogicalKind

Arg : Term 
    | Proof 
    | Predicate 

Stage : '+' | '-'

Variables : Identifier | Variables ',' Variables

Equalities : Term '=' Term | Indentifier | Equalities ',' Equalities 

Termbranches : Dataconstr Variables Term | Termbranches '|' Termbranches

Term : Identifier
     | type int
     | Pi Stage Identifier ':' ArgClass '.' Term  
     | lambda Stage Identifier ':' ArgClass '.' Term
     | let Identifier '=' Term '['Identifier']' in Term     
     | let Identifier '=' Proof in Term 
     | let Identifier '=' Predicate in Term
     | conv Term by '[' Equalities ']' at '['Variables']' '.' Term 
     | case Term '[' Identifier ']'of Termbranches  

     | cast Term by Proof
     | '(' Term Arg ')'
     | abort Term
     | rec Identifier Identifier ':' Term '.' Term
     | Dataconstr



ConstrPair : Dataconstr ':' Term | ConstrPair '|' ConstrPair

Proofbranches : Dataconstr Variables Proof | Proofbranches '|' Proofbranches

Proof : Identifier 
      | inl Proof with Predicate
      | inr Proof with Predicate
      | case Proof of Identifier '.' Proof ',' Identifier '.' Proof
      | Lambda Identifier ':' ArgClass '.' Proof
      | '(' Proof Arg ')'
      | '(' Arg ',' Proof ')' as Predicate
      | case Proof of '(' Identifier ',' Identifier ')' '.' Proof 
      | let Identifier '=' Proof in Proof 
      | let Identifier '=' Term '[' Identifier ']'in Proof 
      | let Identifier '=' Predicate in Proof 
      | join Term Term 
      | conv Proof by Equalities at Variables '.' Predicate
      | predconv Proof Predicate
      | valax Term
      | ord Term Term
      | case Term '[' Identifier ']' Proof  of Proofbranches
      | tcase Term '[' Identifier ']' of abort '=>' Proof '|' '!'
'=>' Proof

      | ind Identifier Identifier ':' Term ',' Proof '.' Proof
      | contr Proof 
      | contraval Proof Proof




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
