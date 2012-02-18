
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
       ProofVar   {TokenProofVar $$}
       PredVar    {TokenPredVar $$}
       TermVar    {TokenTermVar $$}
       formula    {TokeFm }
       Pi         {TokenPi}
       Eq         {TokenEq}
       Bottom     {TokenBot}
       lambda     {TokenLM}
       Lambda     {TokenLamb}
       abort      {TokenAb}
       join {TokenJoin}
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


LogicalKind : Formula int                                            {Formula $2}

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

