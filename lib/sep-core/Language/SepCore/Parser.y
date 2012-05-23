{- The sepcore Parser -}
{
module Language.SepCore.Parser where 
import Language.SepCore.Syntax
import Language.SepCore.Lexer
import Data.Char
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Subst(substR1)
}

%name parser
%tokentype { Token }
%monad{Alex}
%lexer{lexer}{TokenEOF}
%error { parseError }
%token 
       data       {TokenData }
       Data       {TokenData }
       where      {TokenWhere }
       Where      {TokenWhere }
       ProofVar   {TokenProofVar $$}
       PredVar    {TokenPredVar $$}
       TermVar    {TokenTermVar $$}
       int        {TokenInt $$}
       type       {TokenType }
       Type       {TokenType }
       Formula    {TokenFm  }
       formula    {TokenFm }
       Bottom     {TokenBot}
       bottom     {TokenBot}
       Pi         {TokenPi }
       pi         {TokenPi }
       Eq         {TokenEq }
       eq         {TokenEq }
       Forall     {TokenForall }
       forall     {TokenForall}
       '\\'       {TokenLamb }
       abort      {TokenAb }
       Abort      {TokenAb }
       join       {TokenJoin}
       Join       {TokenJoin}
       contr      {TokenContr}
       Contr      {TokenContr}
       valax      {TokenValax }
       Valax      {TokenValax}
       case       {TokenCase}
       Case       {TokenCase}
       of         {TokenOf}
       Of         {TokenOf}
       let        {TokenLet}
       Let        {TokenLet}
       in         {TokenIn}
       In         {TokenIn}
       rec        {TokenRec}
       Rec        {TokenRec}
       '!'        {TokenEx}
       '='        {TokenEquiv}
       '('        {TokenBL}
       ')'        {TokenBR}
       '{'        {TokenCBL}
       '}'        {TokenCBR}
       "::"       {TokenDC}
       '+'        {TokenPlus }
       '-'        {TokenMinus}
       ":="       {TokenDef}
       "->"       {TokenArrow}
       ':'        {TokenCL}
       '.'        {TokenDot}
       '|'        {TokenBar}

%%

Module : Declaration              {[$1]} 
       | Module Declaration       {$1 ++ [$2]}

Declaration : Logicdecl {DeclLogic $1}
            | Proofdef {DeclProof $1}
            | Progdecl {DeclProgdecl $1}
            | Progdef {DeclProgdef $1}
            | Preddecl {DeclPreddecl $1}
            | Preddef {DeclPreddef $1}
            | Datatypedecl  {DeclData $1}

Logicdecl : ProofVar "::" Predicate                  {Logicdecl (ProofVar (string2Name $1)) $3}

Proofdef : ProofVar ":=" Proof                       {Proofdef (ProofVar (string2Name $1)) $3} 

Progdecl : TermVar "::" Term                         {Progdecl (TermVar (string2Name $1)) $3}

Progdef : TermVar ":=" Term                          {Progdef (TermVar (string2Name $1)) $3}

Preddecl : PredVar "::" LogicalKind                  {Preddecl (PredicateVar (string2Name $1)) $3}

Preddef : PredVar ":=" Predicate                        {Preddef (PredicateVar (string2Name $1)) $3}

Datatypedecl : data TermVar "::" Specialterm where Dataconstrs            {Datatypedecl (TermVar (string2Name $2)) (bind $4 $6)}
             | data TermVar "::" Specialterm Where Dataconstrs            {Datatypedecl (TermVar (string2Name $2)) (bind $4 $6)}             
             | Data TermVar "::" Specialterm where Dataconstrs            {Datatypedecl (TermVar (string2Name $2)) (bind $4 $6)}             
             | Data TermVar "::" Specialterm Where Dataconstrs            {Datatypedecl (TermVar (string2Name $2)) (bind $4 $6)}             

Specialterm : Type int     {Empty}
            | type int     {Empty}
            | Pi TermVar ':' Term '.' Specialterm {TCons(rebind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

Dataconstrs : TermVar "::" Term                           {[((ArgNameTerm (string2Name $1)), $3)]}
|  Dataconstrs '|' TermVar "::" Term                      {$1++[((ArgNameTerm (string2Name $3)), $5)]}


{-
Datatypedecl : data TermVar "::" Specialterm where Dataconstrs '.'                          {Datatypedecl (TermVar (string2Name $2)) $4 $6}
             | data TermVar "::" Specialterm Where Dataconstrs '.'                        {Datatypedecl (TermVar (string2Name $2)) $4 $6}
             | Data TermVar "::" Specialterm where Dataconstrs  '.'                        {Datatypedecl (TermVar (string2Name $2)) $4 $6}
             | Data TermVar "::" Specialterm Where Dataconstrs  '.'                       {Datatypedecl (TermVar (string2Name $2)) $4 $6}


Specialterm : Type int     {Type $2}
            | type int     {Type $2}
            | Pi TermVar ':' Stage Term '.' Specialterm {Pi (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $5)) $7) $4}

Dataterm : Appform       {$1}
         | Pi TermVar ':' Stage Term '.' Dataterm  {Pi (bind (ArgNameTerm (string2Name $2), Embed(ArgClassTerm $5)) $7) $4}

Appform : TermVar          {TermVar (string2Name $1)}
        | Appform TermVar   {TermApplication $1 (ArgTerm (TermVar (string2Name $2))) Plus}
        | '(' Appform ')' {$2}

Dataconstrs : TermVar "::" Term                           {[((ArgNameTerm (string2Name $1)), $3)]}
|  Dataconstrs '|' TermVar "::" Term                      {$1++[((ArgNameTerm (string2Name $3)), $5)]}

-}
{-Low level definitions-}

Predicate : PredVar                                    {PredicateVar (string2Name $1)}

| '\\' ProofVar ':' Predicate '.' Predicate            {PredicateLambda (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

| '\\' PredVar ':' LogicalKind '.' Predicate           {PredicateLambda (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| '\\' TermVar ':' Term '.' Predicate                  {PredicateLambda (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}
 
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

LogicalKind : Formula int                              {Formula $2}

            | formula int                              {Formula $2}

            | Forall PredVar ':' LogicalKind '.' LogicalKind        {QuasiForall (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

            | Forall TermVar ':' Term '.' LogicalKind               {QuasiForall (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

            | Forall ProofVar ':' Predicate '.' LogicalKind       {QuasiForall (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)} 

            | forall PredVar ':' LogicalKind '.' LogicalKind        {QuasiForall (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

            | forall TermVar ':' Term '.' LogicalKind               {QuasiForall (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

            | forall ProofVar ':' Predicate '.' LogicalKind       {QuasiForall (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

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

     | case Term of TermBranches {TermCase1 $2 $4}

     | Case Term of TermBranches {TermCase1 $2 $4}

     | case Term Of TermBranches {TermCase1 $2 $4}

     | Case Term Of TermBranches {TermCase1 $2 $4}

     | let ProofVar '=' Proof in Term  {TermLetProof (bind (string2Name $2) $6) $4}

     | Let ProofVar '=' Proof in Term  {TermLetProof (bind (string2Name $2) $6) $4}

     | let ProofVar '=' Proof In Term  {TermLetProof (bind (string2Name $2) $6) $4}

     | Let ProofVar '=' Proof In Term  {TermLetProof (bind (string2Name $2) $6) $4}

     | let TermVar '=' Term in Term {TermLetTerm1 (bind (string2Name $2) $6) $4}

     | Let TermVar '=' Term In Term {TermLetTerm1 (bind (string2Name $2) $6) $4}

     | Let TermVar '=' Term in Term {TermLetTerm1 (bind (string2Name $2) $6) $4}

     | let TermVar '=' Term In Term {TermLetTerm1 (bind (string2Name $2) $6) $4}

     | rec TermVar TermVar ':' Term '.' Term {Rec (bind ((string2Name $2), (string2Name $3), Embed $5) $7)}

     | Rec TermVar TermVar ':' Term '.' Term {Rec (bind ((string2Name $2), (string2Name $3), Embed $5) $7)}

     | '(' Term ')'    {$2}

TermBranches : TermVar "->" Term                    {[(ArgNameTerm (string2Name $1), (bind [] $3))]}
             | TermVar Scheme "->" Term                    {[(ArgNameTerm (string2Name $1), (bind $2 $4))]}
             | TermBranches '|' TermVar Scheme "->" Term       {$1 ++ [(ArgNameTerm (string2Name $3),(bind $4 $6))]}

Scheme : TermVar                               {[ArgNameTerm (string2Name $1)]}
       | ProofVar                              {[ArgNameProof (string2Name $1)]}
       | Scheme TermVar                    {$1 ++ [ArgNameTerm ( string2Name $2)] }
       | Scheme ProofVar                    {$1 ++ [ArgNameProof ( string2Name $2)] }

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

getPosition = Alex (\s -> Right $ (s,alex_pos s))
parseError :: Token -> Alex a
parseError xs = do
                pos@(AlexPn _ line col) <- getPosition
                alexError $  show line ++ ":" ++ show col ++": Parse error: unexpected " ++ (show xs)

--alexMonadScan :: Alex Lexeme
--unLexeme :: Lexeme -> Token
--alexMonadScan :: Alex Lexeme
--alexMonadScan1:: (Lexeme -> Alex a) -> Alex a


lexer :: (Token -> Alex a) -> Alex a
lexer k = do
           l@(L _ tok _) <- alexMonadScan2
           k tok

--test code
test = do putStrLn "Please input an expression:";
         	s <- getLine;
                case runAlex s parser of
                      Left e -> error e
         	      Right a ->putStrLn (show a)

                
        
}
