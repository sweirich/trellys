{- The sepcore Parser -}
{
module Language.SepCore.Parser where 
import Language.SepCore.Syntax
import Language.SepCore.Lexer
import Language.SepCore.PrettyPrint
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
       where      {TokenWhere }
       ProofVar   {TokenProofVar $$}
       PredVar    {TokenPredVar $$}
       TermVar    {TokenTermVar $$}
       int        {TokenInt $$}
       type       {TokenType }
       formula    {TokenFm  }
       bottom     {TokenBot}
       Pi         {TokenPi }
       eq         {TokenEq }
       forall     {TokenForall}
       '\\'       {TokenLamb }
       abort      {TokenAb }
       join       {TokenJoin}
       contr      {TokenContr}
       valax      {TokenValax }
       case       {TokenCase}
       of         {TokenOf}
       let        {TokenLet}
       in         {TokenIn}
       rec        {TokenRec}
       conv       {TokenConv}
       '!'        {TokenEx}
       '='        {TokenEquiv}
       '('        {TokenBL}
       ')'        {TokenBR}
       '{'        {TokenCBL}
       '}'        {TokenCBR}
       '['        {TokenSQL}
       ']'        {TokenSQR}
       "::"       {TokenDC}
       '+'        {TokenPlus }
       '-'        {TokenMinus}
       ":="       {TokenDef}
       "->"       {TokenArrow}
       ':'        {TokenCL}
       '.'        {TokenDot}
       '|'        {TokenBar}
       ','        {TokenComma}
       '@'        {TokenAp}
        by         {TokenBy}
%%

{- A more efficient way is demonstrate below by Garrin. 

Module : Declaration              {[$1]} 
       | Module Declaration       {$1 ++ [$2]}
-}

Module : ModuleRev  { reverse $1 }

ModuleRev : Declaration              {[$1]} 
          | ModuleRev Declaration       {$2 : $1}

Declaration : Logicdecl {DeclLogic $1}
            | Proofdef {DeclProof $1}
            | Progdecl {DeclProgdecl $1}
            | Progdef {DeclProgdef $1}
            | Preddecl {DeclPreddecl $1}
            | Preddef {DeclPreddef $1}
            | Datatypedecl  {DeclData $1}

Logicdecl : ProofVar "::" Predicate '.'                 {Logicdecl (ProofVar (string2Name $1)) $3}

Proofdef : ProofVar ":=" Proof '.'                      {Proofdef (ProofVar (string2Name $1)) $3} 

Progdecl : TermVar "::" Term '.'                        {Progdecl (TermVar (string2Name $1)) $3}

Progdef : TermVar ":=" Term '.'                         {Progdef (TermVar (string2Name $1)) $3}

Preddecl : PredVar "::" LogicalKind '.'                 {Preddecl (PredicateVar (string2Name $1)) $3}

Preddef : PredVar ":=" Predicate'.'                        {Preddef (PredicateVar (string2Name $1)) $3}

Datatypedecl : data TermVar "::" Specialterm where Dataconstrs '.'            {Datatypedecl ($2) (bind $4 $6)}

Specialterm : 
             type int     {Empty}
            | Pi TermVar ':' Stage Term '.' Specialterm  {TCons(rebind (ArgNameTerm (string2Name $2),$4, Embed (ArgClassTerm $5)) $7)}
            | Pi '(' TermVar ':' Stage Term ')' '.' Specialterm {TCons(rebind (ArgNameTerm (string2Name $3),$5, Embed (ArgClassTerm $6)) $9)}
            | Pi ProofVar ':' Stage Predicate '.' Specialterm  {TCons(rebind (ArgNameProof (string2Name $2),$4, Embed (ArgClassPredicate $5)) $7)}
            | Pi '(' ProofVar ':' Stage Predicate ')' '.' Specialterm {TCons(rebind (ArgNameProof (string2Name $3),$5, Embed (ArgClassPredicate $6)) $9)}

Dataconstrs : TermVar "::" Term                           {[($1, $3)]}
|  Dataconstrs '|' TermVar "::" Term                      {$1++[($3, $5)]}



{-Low level definitions-}

InnerPredicate : PredVar                                    {PredicateVar (string2Name $1)}

| '\\' ProofVar ':' Predicate '.' Predicate            {PredicateLambda (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

| '\\' PredVar ':' LogicalKind '.' Predicate           {PredicateLambda (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| '\\' TermVar ':' Term '.' Predicate                  {PredicateLambda (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| forall PredVar ':' LogicalKind '.' Predicate         {Forall (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| forall TermVar ':' Term '.' Predicate                {Forall (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| forall ProofVar ':' Predicate '.' Predicate          {Forall (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

{-
| '(' Predicate Proof ')'                              {PredicateApplication $2 (ArgProof $3)}

| '(' Predicate Term ')'                               {PredicateApplication $2 (ArgTerm $3)}

| '(' Predicate Predicate ')'                          {PredicateApplication $2 (ArgPredicate $3)}
-}

| '{' Term ',' Term '}'                                      {Equal $2 $4}

| '!' Term                                             {Terminate $2}

| bottom  int                                          {Bottom $2}

| '(' Predicate ')'                                    {$2}

Predicate : GetPos SpineFormPredicate {PosPredicate $1 $2}

SpineFormPredicate : InnerPredicate PredicateArgs  { foldr ( \ x f -> PredicateApplication f  x) $1 $2}

PredicateArg : InnerTerm    {ArgTerm $1}
        | InnerProof   {ArgProof $1}
        | InnerPredicate       { ArgPredicate $1}

PredicateArgs : { [] }
         | PredicateArgs PredicateArg  { $2 : $1 }

InnerLogicalKind : 

            formula int                              {Formula $2}

            | forall PredVar ':' LogicalKind '.' LogicalKind        {QuasiForall (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

            | forall TermVar ':' Term '.' LogicalKind               {QuasiForall (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

            | forall ProofVar ':' Predicate '.' LogicalKind       {QuasiForall (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

            | '(' LogicalKind ')'                       {$2}
     
LogicalKind : GetPos InnerLogicalKind {PosLK $1 $2}  

Stage : '+'  {Plus}
      | '-'  {Minus}


InnerTerm : TermVar   {(TermVar (string2Name $1))}
   
     | type int  {Type $2}

     | Pi PredVar ':' Stage LogicalKind '.' Term  {Pi (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $5)) $7) $4}
   
     | Pi TermVar ':' Stage Term '.' Term         {Pi (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $5)) $7) $4}

     | Pi ProofVar ':' Stage Predicate '.' Term   {Pi (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $5)) $7) $4}

     | Pi '(' PredVar ':' Stage LogicalKind ')' '.' Term  {Pi (bind (ArgNamePredicate (string2Name $3), Embed (ArgClassLogicalKind $6)) $9) $5}
   
     | Pi '(' TermVar ':' Stage Term ')' '.' Term        {Pi (bind (ArgNameTerm (string2Name $3), Embed (ArgClassTerm $6)) $9) $5}

     | Pi '('ProofVar ':' Stage Predicate')' '.' Term   {Pi (bind (ArgNameProof (string2Name $3), Embed (ArgClassPredicate $6)) $9) $5}

     | '\\' TermVar ':' Stage Term '.' Term        {TermLambda (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $5)) $7) $4}
 
     | '\\' ProofVar ':' Stage Predicate '.' Term  {TermLambda (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $5)) $7) $4}

     | '\\' PredVar ':' Stage LogicalKind '.' Term {TermLambda (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $5)) $7) $4}

     | '\\''(' TermVar ':' Stage Term ')' '.' Term        {TermLambda (bind (ArgNameTerm (string2Name $3), Embed (ArgClassTerm $6)) $9) $5}
 
     | '\\''(' ProofVar ':' Stage Predicate ')''.' Term  {TermLambda (bind (ArgNameProof (string2Name $3), Embed (ArgClassPredicate $6)) $9) $5}

     | '\\' '(' PredVar ':' Stage LogicalKind ')' '.' Term {TermLambda (bind (ArgNamePredicate (string2Name $3), Embed (ArgClassLogicalKind $6)) $9) $5}
 
     | abort Term      {Abort $2}

     | case Term of TermBranches {TermCase1 $2 $4}

     | let ProofVar '=' Proof in Term  {TermLetProof (bind (string2Name $2) $6) $4}

     | let TermVar '=' Term in Term {TermLetTerm1 (bind (string2Name $2) $6) $4}

     | rec TermVar TermVar ':' Term '.' Term {Rec (bind ((string2Name $2), (string2Name $3), Embed $5) $7)}

     | conv  Term by Proof '@' TermVar '.'  Term  {Conv $2 $4 (bind (string2Name $6) $8)}

     | '(' Term ')' {$2}

{-
 Another way to implement spine form is demonstrated by Garrin below:
Term : SpineForm {$1}

GetPos : { %do pos<-getPosition; return pos}

SpineForm :  GetPos InnerTerm      { Pos $1 $2 }
          | SpineForm InnerTerm {TermApplication $1 (ArgTerm $2) Plus}
          | SpineForm '['InnerTerm']' {TermApplication $1 (ArgTerm $3) Minus}
          | '(' SpineForm ')' {$2}
-}

GetPos : {% getPosition}

Term : GetPos SpineForm {Pos $1 $2}

SpineForm : InnerTerm TermArgs  { foldr ( \ (pm, x) f -> TermApplication f x pm) $1 $2}

TermArg : '['Term']'    { (Minus, (ArgTerm $2))}
        |'['Proof']'    { (Minus, (ArgProof $2))}
        | '['Predicate']'    { (Minus, (ArgPredicate $2))}
        | InnerTerm       { (Plus, (ArgTerm $1))}

TermArgs : { [] }
         | TermArgs TermArg  { $2 : $1 }



TermBranches : TermVar "->" Term                    {[($1, (bind [] $3))]}
             | TermVar Scheme "->" Term                    {[($1, (bind $2 $4))]}
             | TermBranches '|' TermVar Scheme "->" Term       {$1 ++ [($3,(bind $4 $6))]}

Scheme : TermVar                               {[(ArgNameTerm (string2Name $1), Plus)]}
       | ProofVar                              {[(ArgNameProof (string2Name $1),Minus )]}
       | '['TermVar']'                         {[(ArgNameTerm (string2Name $2),Minus )]}
       | Scheme TermVar                    {$1 ++ [(ArgNameTerm ( string2Name $2), Plus)] }
       | Scheme ProofVar                    {$1 ++ [(ArgNameProof ( string2Name $2),Minus )] }
       | Scheme '['TermVar']'              {$1 ++ [(ArgNameTerm ( string2Name $3), Minus)] }

InnerProof : ProofVar                                    {ProofVar (string2Name $1)}

| '\\' ProofVar ':' Predicate '.' Proof          {ProofLambda (bind (ArgNameProof (string2Name $2), Embed (ArgClassPredicate $4)) $6)}

| '\\' PredVar ':' LogicalKind '.' Proof         {ProofLambda (bind (ArgNamePredicate (string2Name $2), Embed (ArgClassLogicalKind $4)) $6)}

| '\\' TermVar ':' Term '.' Proof                {ProofLambda (bind (ArgNameTerm (string2Name $2), Embed (ArgClassTerm $4)) $6)}

| '['Term ',' Term ']'                                    {Join $2 $4}


{-

| '(' Proof Term ')'                                {ProofApplication $2 (ArgTerm $3)}

| '(' Proof Proof ')'                               {ProofApplication $2 (ArgProof $3)}

| '(' Proof Predicate ')'                           {ProofApplication $2 (ArgPredicate $3)}

  -}

| contr Proof                                       {Contra $2}

| valax Term                                        {Valax $2}

| '(' Proof ')'                                     {$2}

Proof : GetPos SpineFormProof {PosProof $1 $2}

SpineFormProof : InnerProof ProofArgs  { foldr ( \ x f -> ProofApplication f  x) $1 $2}

ProofArg : InnerTerm    {ArgTerm $1}
        | InnerPredicate    {ArgPredicate $1}
        | InnerProof       { ArgProof $1}

ProofArgs : { [] }
         | ProofArgs ProofArg  { $2 : $1 }



{

getPosition = Alex (\s -> Right $ (s,alex_pos s))
parseError :: Token -> Alex a
parseError xs = do
                pos@(AlexPn _ line col) <- getPosition
		alexError $  show line ++ ":" ++ show (col-length(show(disp xs))-1) ++": Parse error: unexpected " ++ show(disp xs)

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

