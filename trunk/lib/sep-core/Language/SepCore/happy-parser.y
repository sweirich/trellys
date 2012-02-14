
{- The sepcore Parser -}

{
module Main  where
import Data.Char
}

%name sepcore-parser
%tokentype { Token }
%error { parseError }

%token 
       type       {TokenType}
       data       {TokenData}
       string     {TokenString $$}
       int        {TokenInt $$}
       where      {TokenWhere}
       theorem    {TokenTheorem}
       Var         {TokenVar $$}
       Pi         {TokenPi}
       Eq         {TokenEq}
       Bottom     {TokenBot}
       '!'        {TokenEx}
       '('        {TokenBL}
       ')'        {TokenBR}
       '['        {TokenBll}
       ']'        {TokenBrr}
       "::"       {TokenDC}
       '+'        {TokenPlus}
       '-'        {TokenMinus}
       ":="       {TokenDef}
       ':'        {TokenCL}
       '.'        {TokenDot}





%%

{-Top level definitions and declarations -}

Logicdecl : ProofVar "::" Predicate  {Logicdecl $1 $3}

ProofVar : theorem Var {$2} 

Predicate : '[' Var ']'                          {PredicateVar (string2Name $2)}
 | Lambda Var ':' Predicate '.' Predicate     {PredicateLambda (Bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}
 | Lambda Var ':' LogicalKind '.' Predicate {PredicateLambda (Bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}
 | Lambda Var ':' Term '.' Predicate {PredicateLambda (Bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}
 
| Forall Var ':' LogicalKind '.' Predicate {Forall (Bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| Forall Var ':' Term '.' Predicate      {Forall (Bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| Forall Var ':' Predicate '.' Predicate {Forall (Bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}
  
| '(' Predicate Proof ')' {PredicateApplication $2 (ArgProof $3)}
          | '(' Predicate Term ')' {PredicateApplication $2 (ArgTerm $3)}
          | '(' Predicate Predicate ')' {PredicateApplication $2 (ArgPredicate $3)}
          | Eq Term Term      {Equal $2 $3}
| '!' Term     {Terminate $2}
| Bottom  int {Bottom $2}


LogicalKind :            


Term : 


{
parseError :: [Token] -> a
parseError _ = error "Parse error"

 data Logicdecl = Logicdecl String Predicate 
             deriving (Show)
  
 data Predicate = PredicateVar String

                | PredicateLambda String  Predicate
                
                | PredicateApplication 
                | Forall 


{- Our temp main loop. -}
main = getContents >>= print . sepcore-parser . lexer

}

