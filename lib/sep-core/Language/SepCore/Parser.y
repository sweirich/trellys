{- The sepcore Parser -}
{
module Language.SepCore.Happyparser where 
import Language.SepCore.Syntax
import Data.Char
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Subst(substR1)
}

%name parser Predicate
%name parser4Logicdecl Logicdecl
%name parser4Proofdef Proofdef
%name parser4Progdecl Progdecl
%name parser4Progdef Progdef
%name parser4Preddecl Preddecl
%name parser4Preddef Preddef
%name parser4Prf Proof
%name parser4Term Term
%name parser4LK LogicalKind

%name parser4Datatypedecl Datatypedecl
%name parser4Dataconstr Dataconstr
%tokentype { Token }
%error { parseError }

%token 
       Id         {TokenId $$}
       ProofVar   {TokenProofVar $$}
       PredVar    {TokenPredVar $$}
       TermVar    {TokenTermVar $$}
       int        {TokenInt $$}
       type       {TokenType}
       Type       {TokenType}
       Formula    {TokenFm}
       formula    {TokenFm}
       Bottom     {TokenBot}
       bottom     {TokenBot}
       Pi         {TokenPi}
       pi         {TokenPi}
       Eq         {TokenEq}
       eq         {TokenEq}
       Forall     {TokenForall}
       forall     {TokenForall}
       '\\'       {TokenLamb}
       abort      {TokenAb}
       Abort      {TokenAb}
       join       {TokenJoin}
       Join       {TokenJoin}
       contr      {TokenContr}
       Contr      {TokenContr}
       valax      {TokenValax}
       Valax      {TokenValax}
       '!'        {TokenEx}
       '('        {TokenBL}
       ')'        {TokenBR}
       '{'        {TokenCBL}
       '}'        {TokenCBR}
       "::"       {TokenDC}
       '+'        {TokenPlus}
       '-'        {TokenMinus}
       ":="       {TokenDef}
       ':'        {TokenCL}
       '.'        {TokenDot}

%%

{-Top level definitions and declarations -}

Logicdecl : Id "::" Predicate                    {Logicdecl (string2Name $1) $3}

Proofdef : Id ":=" Proof                          {Proofdef (string2Name $1) $3} 

Progdecl : Id "::" Term                           {Progdecl (string2Name $1) $3}

Progdef : Id ":=" Term                             {Progdef (string2Name $1) $3}

Preddecl : Id "::" LogicalKind                    {Preddecl (string2Name $1) $3}

Preddef : Id ":=" Predicate                        {Preddef (string2Name $1) $3}

Datatypedecl : Id ':' Term                         {Datatypedecl (string2Name $1) $3}

Dataconstr : Id ':' Term                           {Dataconstr (string2Name $1) $3}

{-Low level definitions-}

Predicate : PredVar                                    {PredicateVar (string2Name $1)}

| '\\' ProofVar ':' Predicate '.' Predicate          {PredicateLambda (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

| '\\' PredVar ':' LogicalKind '.' Predicate         {PredicateLambda (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| '\\' TermVar ':' Term '.' Predicate                {PredicateLambda (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}
 
| Forall PredVar ':' LogicalKind '.' Predicate         {Forall (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| Forall TermVar ':' Term '.' Predicate                {Forall (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| Forall ProofVar ':' Predicate '.' Predicate          {Forall (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

| forall PredVar ':' LogicalKind '.' Predicate         {Forall (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| forall TermVar ':' Term '.' Predicate                {Forall (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| forall ProofVar ':' Predicate '.' Predicate          {Forall (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}
  
| '(' Predicate Proof ')'                              {PredicateApplication $2 (ArgProof $3)}

| '(' Predicate Term ')'                               {PredicateApplication $2 (ArgTerm $3)}

| '(' Predicate Predicate ')'                          {PredicateApplication $2 (ArgPredicate $3)}

| Eq Term Term                                         {Equal $2 $3}

| eq Term Term                                         {Equal $2 $3}

| '!' Term                                             {Terminate $2}

| Bottom  int                                          {Bottom $2}

| bottom  int                                          {Bottom $2}

| '(' Predicate ')'                                    {$2}

LogicalKind : Formula int                           {Formula $2}

            | formula int                           {Formula $2}

            | Forall LogicalKind '.' LogicalKind        {QuasiForall (ArgClassLogicalKind $2) $4}

            | Forall  Term '.' LogicalKind               {QuasiForall (ArgClassTerm $2) $4}

            | Forall  Predicate '.' LogicalKind         {QuasiForall (ArgClassPredicate $2) $4}

            | forall LogicalKind '.' LogicalKind        {QuasiForall (ArgClassLogicalKind $2) $4}

            | forall  Term '.' LogicalKind               {QuasiForall (ArgClassTerm $2) $4}

            | forall  Predicate '.' LogicalKind         {QuasiForall (ArgClassPredicate $2) $4}

            | '(' LogicalKind ')'                       {$2}
       
Stage : '+'  {Plus}
      | '-'  {Minus}


Term : TermVar   {TermVar (string2Name $1)}
   
     | type int  {Type $2}

     | Type int  {Type $2}

     | Pi PredVar ':' Stage LogicalKind '.' Term  {Pi (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $5)) $7) $4}
   
     | Pi TermVar ':' Stage Term '.' Term         {Pi (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $5)) $7) $4}

     | Pi ProofVar ':' Stage Predicate '.' Term   {Pi (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $5)) $7) $4}

     | pi PredVar ':' Stage LogicalKind '.' Term  {Pi (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $5)) $7) $4}
   
     | pi TermVar ':' Stage Term '.' Term         {Pi (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $5)) $7) $4}

     | pi ProofVar ':' Stage Predicate '.' Term   {Pi (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $5)) $7) $4}

     | '(' Stage Term Term ')'                    {TermApplication $3 (ArgTerm $4) $2}

     | '(' Stage Term Proof ')'                   {TermApplication $3 (ArgProof $4) $2}

     | '(' Stage Term Predicate ')'               {TermApplication $3 (ArgPredicate $4) $2}

     | '\\' TermVar ':' Stage Term '.' Term        {TermLambda (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $5)) $7) $4}
 
     | '\\' ProofVar ':' Stage Predicate '.' Term  {TermLambda (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $5)) $7) $4}

     | '\\' PredVar ':' Stage LogicalKind '.' Term {TermLambda (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $5)) $7) $4}
 
     | abort Term      {Abort $2}

     | Abort Term      {Abort $2}

     | '(' Term ')'    {$2}


Proof : ProofVar                                    {ProofVar (string2Name $1)}

| '\\' ProofVar ':' Predicate '.' Proof          {ProofLambda (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

| '\\' PredVar ':' LogicalKind '.' Proof         {ProofLambda (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| '\\' TermVar ':' Term '.' Proof                {ProofLambda (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| join Term Term                                    {Join $2 $3}

| Join Term Term                                    {Join $2 $3}

| '(' Proof Term ')'                                {ProofApplication $2 (ArgTerm $3)}

| '(' Proof Proof ')'                               {ProofApplication $2 (ArgProof $3)}

| '(' Proof Predicate ')'                           {ProofApplication $2 (ArgPredicate $3)}

| contr Proof                                       {Contra $2}

| Contr Proof                                       {Contra $2}

| valax Term                                        {Valax $2}

| Valax Term                                        {Valax $2}

| '(' Proof ')'                                     {$2}

{
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
  deriving (Show)

parseError :: [Token] -> a
parseError _ = error "Parse error blah blah"

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
      | isSpace c = lexer cs
      | isAlpha c = lexVar (c:cs)
      | isDigit c = lexNum (c:cs)

lexer ('!': cs) = TokenEx : lexer cs 
lexer ('\\': cs) = TokenLamb : lexer cs 
lexer ('=': cs) = TokenEq : lexer cs 
lexer ('.': cs) = TokenDot : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer ('-':cs) = TokenMinus : lexer cs
lexer ('(':cs) = TokenBL : lexer cs
lexer (')':cs) = TokenBR : lexer cs
lexer ('{':cs) = TokenCBL : lexer cs
lexer ('}':cs) = TokenCBR : lexer cs


lexer (':': cs) = case cs of
		  (':': css) -> TokenDC : lexer css
		  ('=': css) -> TokenDef : lexer cs
                  ( _ : css) -> TokenCL : lexer cs
		 
lexer ('$': cs) = case span isAlpha cs of
		  (proofvar, rest) -> TokenProofVar proofvar : lexer rest 

lexer ('#': cs) = case span isAlpha cs of
		  (predvar, rest) -> TokenPredVar predvar : lexer rest 

lexer ('@': cs) = case span isAlpha cs of
		  (termvar, rest) -> TokenTermVar termvar : lexer rest 



lexNum cs = TokenInt (read num) : lexer rest
      where (num,rest) = span isDigit cs

lexVar cs =
    case span isAlpha cs of
      ("valax",rest) -> TokenValax : lexer rest
      ("Valax",rest) -> TokenValax : lexer rest
      ("contr",rest)  -> TokenContr : lexer rest
      ("Contr",rest)  -> TokenContr : lexer rest
      ("join",rest)  -> TokenJoin : lexer rest
      ("Join",rest)  -> TokenJoin : lexer rest
      ("abort",rest)  -> TokenAb : lexer rest
      ("Abort",rest)  -> TokenAb : lexer rest
      ("Bottom",rest)  -> TokenBot : lexer rest
      ("bottom",rest)  -> TokenBot : lexer rest
      ("Pi",rest)  -> TokenPi : lexer rest
      ("pi",rest)  -> TokenPi : lexer rest
      ("formula",rest)  -> TokenFm : lexer rest
      ("Formula",rest)  -> TokenFm : lexer rest
      ("type",rest)  -> TokenType : lexer rest
      ("Type",rest)  -> TokenType : lexer rest
      ("Forall",rest) -> TokenForall : lexer rest
      ("forall",rest) -> TokenForall : lexer rest

      (var,rest) -> TokenId var : lexer rest
      
-- For test purpose
readinput1 = do putStrLn "Please input a predicate"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser( lexer inpStr))

readinput2 = do putStrLn "Please input a proof"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Prf( lexer inpStr))

readinput3 = do putStrLn "Please input a term"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Term( lexer inpStr))

readinput4 = do putStrLn "Please input a LogicalKind"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4LK( lexer inpStr))

readinput5 = do putStrLn "Please input a Proof declaration"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Logicdecl( lexer inpStr))

readinput6 = do putStrLn "Please input a Proof definition"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Proofdef( lexer inpStr))

readinput7 = do putStrLn "Please input a Program declaration"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Progdecl( lexer inpStr))

readinput8 = do putStrLn "Please input a Program definition"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Progdef( lexer inpStr))

readinput9 = do putStrLn "Please input a Predicate declaration"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Preddecl( lexer inpStr))

readinput10 = do putStrLn "Please input a Predicate definition"
                 inpStr <- getLine 
                 putStrLn $ "Here is the result: " ++ show(parser4Preddef( lexer inpStr))






}

