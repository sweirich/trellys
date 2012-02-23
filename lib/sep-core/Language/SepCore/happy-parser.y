
{- The sepcore Parser -}
{
module Main where 
import Language.SepCore.Syntax
import Data.Char
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Subst(substR1)

}

%name parser
%tokentype { Token }
%error { parseError }

%token 
       type       {TokenType}
       data       {TokenData}
       int        {TokenInt $$}
       theorem    {TokenTheorem}
       ProofVar   {TokenProofVar $$}
       PredVar    {TokenPredVar $$}
       TermVar    {TokenTermVar $$}
       formula    {TokeFm }
       Pi         {TokenPi}
       Eq         {TokenEq}
       Bottom     {TokenBot}
       lambda     {TokenLM}
       Lambda     {TokenLamb}
       Forall     {TokenForall}
       Qforall    {TokenQF}
       plambda    {TokenPlam}
       abort      {TokenAb}
       join       {TokenJoin}
       contr      {TokenContr}
       valax      {TokenValax}
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

Logicdecl : ProofVar "::" Predicate                    {Logicdecl $1 $3}

Predicate : PredVar                                    {PredicateVar (string2Name $1)}

| Lambda ProofVar ':' Predicate '.' Predicate          {PredicateLambda (Bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

| Lambda PredVar ':' LogicalKind '.' Predicate         {PredicateLambda (Bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| Lambda TermVar ':' Term '.' Predicate                {PredicateLambda (Bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}
 
| Forall PredVar ':' LogicalKind '.' Predicate         {Forall (Bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| Forall TermVar ':' Term '.' Predicate                {Forall (Bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| Forall ProofVar ':' Predicate '.' Predicate          {Forall (Bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}
  
| '(' Predicate Proof ')'                              {PredicateApplication $2 (ArgProof $3)}


| '(' Predicate Term ')'                               {PredicateApplication $2 (ArgTerm $3)}

| '(' Predicate Predicate ')'                          {PredicateApplication $2 (ArgPredicate $3)}

| Eq Term Term                                         {Equal $2 $3}

| '!' Term                                             {Terminate $2}

| Bottom  int                                          {Bottom $2}


LogicalKind : formula int                                            {Formula $2}

            | Qforall PredVar ':' LogicalKind '.' LogicalKind        {QuasiForall (Bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

            | Qforall TermVar ':' Term '.' LogicalKind               {QuasiForall (Bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

            | Qforall ProofVar ':' Predicate '.' LogicalKind         {QuasiForall (Bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}


       
Stage : '+'  {Plus}
      | '-'  {Minus}


Term : TermVar   {TermVar (string2name $1)}
   
     | type int  {Type $2}

     | Pi PredVar ':' Stage LogicalKind '.' Term  {Pi (Bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $5)) $7) $4}
   
     | Pi TermVar ':' Stage Term '.' Term         {Pi (Bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $5)) $7) $4}

     | Pi ProofVar ':' Stage Predicate '.' Term   {Pi (Bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $5)) $7) $4}

     | '(' Stage Term Term ')'                    {TermApplication $3 (ArgTerm $4) $2}

     | '(' Stage Term Proof ')'                   {TermApplication $3 (ArgProof $4) $2}

     | '(' Stage Term Predicate ')'               {TermApplication $3 (ArgPredicate $4) $2}

     | lambda TermVar ':' Stage Term '.' Term     {TermLambda (Bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $5)) $7) $4}
 
     | lambda ProofVar ':' Stage Predicate '.' Term {TermLambda (Bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $5)) $7) $4}

     | lambda PredVar ':' Stage LogicalKind '.' Term {TermLambda (Bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $5)) $7) $4}
 
     | abort Term      {Abort $2}




Proof : ProofVar                                    {ProofVar (string2Name $1)}

| plambda ProofVar ':' Predicate '.' Proof          {ProofLambda (Bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

| plambda PredVar ':' LogicalKind '.' Proof         {ProofLambda (Bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| plambda TermVar ':' Term '.' Proof                {ProofLambda (Bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| join Term Term                                    {Join $2 $3}

| '(' Proof Term ')'                                {ProofApplication $2 (ArgTerm $3)}

| '(' Proof Proof ')'                               {ProofApplication $2 (ArgProof $3)}

| '(' Proof Predicate ')'                           {ProofApplication $2 (ArgPredicate $3)}

| contr Proof                                       {Contra $2}

| valax Term                                        {Valax $2}


{
data Token =

       TokenType

       | TokenData

       | TokenInt Integer

       | TokenForall
 
       | TokenQF
 
       | TokenPlam

       | TokenTheorem

       | TokenProofVar String

       | TokenPredVar String

       | TokenTermVar String

       | TokeFm 

       | TokenPi

       | TokenEq

       | TokenBot

       | TokenLM

       | TokenLamb

       | TokenAb

       | TokenJoin

       | TokenContr

       | TokenValax

       | TokenEx

       | TokenBL

       | TokenBR

       | TokenBll

       | TokenBrr

       | TokenDC

       | TokenPlus

       | TokenMinus

       | TokenDef

       | TokenCL

       | TokenDot

		  deriving (Show)

parseError :: [Token] -> a
parseError _ = error "Parse error"


lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
      | isSpace c = lexer cs
      | isAlpha c = lexVar (c:cs)
      | isDigit c = lexNum (c:cs)

lexer ('!': cs) = TokenEx : lexer cs 
lexer ('[': cs) = TokenBll : lexer cs
lexer (']': cs) = TokenBrr : lexer cs
lexer ('.': cs) = TokenDot : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer ('-':cs) = TokenMinus : lexer cs
lexer ('(':cs) = TokenOB : lexer cs
lexer (')':cs) = TokenCB : lexer cs
lexer (':': cs) = case cs of
		  (':': css) -> TokenDC : lexer css
		  ('=': css) -> TokenDef : lexer css
		  ( _ : css) -> TokenCL : lexer cs
		 
lexer ('$': cs) = case span isAlpha cs of
		  (proofvar, rest) -> TokenProofVar proofvar : lexer rest 

lexer ('#': cs) = case span isAlpha cs of
		  (predvar, rest) -> TokenPredVar predvar : lexer rest 


lexNum cs = TokenInt (read num) : lexer rest
      where (num,rest) = span isDigit cs

lexVar cs =
    case span isAlpha cs of
      ("valax",rest) -> TokenValax : lexer rest
      ("contr",rest)  -> TokenContr : lexer rest
      ("join",rest)  -> TokenJoin : lexer rest
      ("abort",rest)  -> TokenAb : lexer rest
      ("Lambda",rest)  -> TokenLamb : lexer rest
      ("lambda",rest)  -> TokenLM : lexer rest
      ("Bottom",rest)  -> TokenBot : lexer rest
      ("Eq",rest)  -> TokenEq : lexer rest
      ("Pi",rest)  -> TokenPi : lexer rest
      ("formula",rest)  -> TokenFm : lexer rest
      ("type",rest)  -> TokenType : lexer rest
      ("data",rest)  -> TokenData : lexer rest
      ("theorem",rest)  -> TokenTheorem : lexer rest
      (var,rest) -> TokenTermVar var : lexer rest
      


{- Our temp main loop. -}
main = getContents >>= print . parser . lexer

}

