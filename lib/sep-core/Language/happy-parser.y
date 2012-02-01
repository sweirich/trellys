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
       exist
       bottom

        '<'
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
        "->"
%%

{-Top level definitions and declarations -}

Datadecl : data Identifier Term where ConstrPair             {Datadecl (DataConstr $2) $3 $5 }

Theoremdecl : theorem Identifier "::" Predicate              {Theoremdecl (ProofVar (string2Name $2)) $4 }

Proofdef : proof Identifier ":=" Proof                       {Proofdef (ProofVar (string2Name $2)) $4}

Typedecl : type Identifier "::" Term                         {Typedef (TermVar (string2Name $2)) $4}

Progdef : term Identifier ":=" Term                          {Progdef (TermVar (string2Name $2)) $4}

LogicalKinddecl : kind Identifier "::" LogicalKind           {LogicalKinddecl (PredicateVar (string2Name $2)) $4}

Predicatedef : predicate Identifier ":=" Predicate           {Predicatedef (PredicateVar (string2Name $2)) $4}

{-Non Top level definitions-}

Identifier : string    {}

Dataconstr : string    {}


ArgClass : Term 
         | Predicate
         | LogicalKind

Arg : Term 
    | Proof 
    | Predicate 

Stage : '+'
      | '-'

Variables : Identifier
          | Variables ',' Identifier


Equalities : Term '=' Term
           | Identifier
           | Equalities ',' Identifier 
           | Equalities ',' Term '=' Term

Termbranches : Dataconstr Variables Term 
             | Termbranches '|' Dataconstr Variables Term

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



ConstrPair : Dataconstr ':' Term | ConstrPair '|' Dataconstr ':' Term

Proofbranches : Dataconstr Variables Proof 
              | Proofbranches '|' Dataconstr Variables Proof

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
            |  ArgClass "->" LogicalKind 

Predicate : Identifier
          | Lambda Identifier ':' ArgClass '.' Predicate
          | '(' Predicate Arg ')'
          | forall Identifier ':' ArgClass '.' Predicate
          | let Identifier '=' Proof in Predicate         
          | let Identifier '=' Predicate in Predicate
          | let Identifier '=' Term '[' Identifier ']' in Predicate

          | Term '=' Term
          | '!' Term
          | Predicate '+' Predicate
          | exist Identifier ':' ArgClass '.' Predicate
          | bottom int
          | Term '<' Term


           
{
parseError :: [Token] -> a
parseError _ = error "Parse error"


data Datadecl = Datadecl Term Term Dataconstr
  deriving (Show)

type Dataconstr = [(Identifier, Term)]

type Identifier = String  

data Theoremdecl = Theoremdecl Proof Predicate 
  deriving (Show)



data Stage = Plus | Minus deriving(Show)

data SuperKind = Logical Integer deriving (Show)

data LogicalKind = Formula Integer

         | QuasiForall ArgClass LogicalKind

  deriving(Show)

data Predicate = PredicateVar (Name Predicate)

           | PredicateLambda (Bind (ArgName, Embed ArgClass) Predicate)

           | PredicateApplication Predicate Arg

           | Forall (Bind (ArgName, Embed ArgClass) Predicate)

           | PredicateLetProof (Bind (Name Proof) Predicate) Proof

           | PredicateLetPredicate (Bind (Name Predicate) Predicate) Predicate

           | PredicateLetTerm (Bind (Name Term, Name Proof) Predicate) Term

           | Equal Term Term

           | Terminate Term

           | Disjunction Predicate Predicate

           | Exist (Bind (ArgName, Embed ArgClass) Predicate)

           | Bottom Integer

           | Order Term Term

  deriving(Show)

data Proof =  ProofVar (Name Proof)

             | InjectLeft Proof Predicate

             | InjectRight Proof Predicate

             | DisjunctionElimination (Bind (Name Proof) Proof) (Bind (Name Proof) Proof) Proof
             
             | ProofLambda (Bind (ArgName, Embed ArgClass) Proof)

             | ProofApplication Proof Arg

             | ExistentialIntroduction (Arg, Proof) Predicate

             | ExistentialElimination Proof (Bind (ArgName, Name Predicate) Proof)

             | ProofLetProof (Bind (Name Proof) Proof) Proof

             | ProofLetPredicate (Bind (Name Predicate) Proof) Predicate

             | ProofLetTerm (Bind (Name Term, Name Proof) Proof) Term --Bind a term var and a proof var in a proof.

             | Join Term Term

             | ConvProof Proof [Equality] (Bind [(Name Term)] Predicate) 

             | Valax Term

             | ProofOrder Term Term

             | ProofCase Term Proof (Bind (Name Proof)  [(Term, [ArgName],Proof )])
 
             | TerminationCase Term (Bind (Name Proof) (Proof,Proof)) 

             | Ind (Bind (Name Term, Name Proof, Embed Term, Name Proof) Proof)

--bind three variable in a proof

             | Contra Proof
            
             | Contraval Proof Proof


    deriving(Show)

data Equality = Equality Predicate
            
              | EqualityProof Proof

    deriving(Show)    

data Term =  TermVar (Name Term)

           | Type Integer

           | Pi (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermLambda (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermLetTerm (Bind (Name Term, Name Proof) Term) Term

           | TermLetProof (Bind (Name Proof) Term) Proof

           | TermLetPredicate ((Bind (Name Predicate) Term)) Predicate

           | ConvTerm Term [Equality] (Bind [(Name Term)] Term)

           | TermCase Term (Bind (Name Term)  [(Term, [ArgName],Term)])

           | Tcast Term Proof

           | TermApplication Term Arg Stage

           | DataConstr String

           | Abort Term

           | Rec (Bind (Name Term, Name Term, Embed Term) Term)

--bind two term in a term.

  deriving(Show)

data ArgClass = ArgClassTerm Term

               | ArgClassPredicate Predicate

               | ArgClassLogicalKind LogicalKind

      deriving(Show)

data Arg = ArgTerm Term

          | ArgProof Proof

          | ArgPredicate Predicate
 
        deriving(Show)

data ArgName = ArgNameProof (Name Proof)
           
          | ArgNameTerm (Name Term)
        
          | ArgNamePredicate (Name Predicate)   

         deriving Show


data Value = Value | NonValue deriving (Show)


         

$(derive [''Proof,''Term, ''Predicate, ''Arg, ''ArgName, ''Stage, ''Value, ''ArgClass, ''LogicalKind, ''Equality])

type TypingContext = [(ArgName, ArgClass,Value )]

instance Subst LogicalKind Stage
instance Subst LogicalKind ArgName
instance Subst LogicalKind Value
instance Subst LogicalKind Arg
instance Subst LogicalKind ArgClass
instance Subst LogicalKind Predicate
instance Subst LogicalKind Term
instance Subst LogicalKind Proof
instance Subst LogicalKind LogicalKind
instance Subst LogicalKind Equality

instance Subst Arg Stage
instance Subst Arg ArgName
instance Subst Arg ArgClass
instance Subst Arg LogicalKind
instance Subst Arg Arg 

instance Subst Arg Predicate where
  subst n (ArgPredicate pd) prd = subst (translate n) pd prd
  subst n a prd = substR1 rep1 n a prd

-- | here we do a implicit mutually recursive call on the 'substR1' defined in (Subst Arg Term) and (Subst Arg Proof)

instance Subst Arg Term where
  subst n (ArgTerm t) tm = subst (translate n) t tm
  subst n a tm = substR1 rep1 n a tm

instance Subst Arg Proof where
  subst n (ArgProof p) pf = subst (translate n) p pf
  subst n a pf = substR1 rep1 n a pf

instance Subst Arg Equality

instance Subst Proof Arg
instance Subst Proof ArgName
instance Subst Proof Term 
instance Subst Proof Predicate 
instance Subst Proof Stage
instance Subst Proof LogicalKind
instance Subst Proof Value
instance Subst Proof ArgClass
instance Subst Proof Equality
instance Subst Proof Proof where
  isvar (ProofVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Term Arg
instance Subst Term ArgClass
instance Subst Term ArgName
instance Subst Term Proof 
instance Subst Term Equality
instance Subst Term Predicate 
instance Subst Term LogicalKind
instance Subst Term Stage
instance Subst Term Value
instance Subst Term Term where
  isvar (TermVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Predicate Term 
instance Subst Predicate Proof
instance Subst Predicate Equality
instance Subst Predicate LogicalKind
instance Subst Predicate Stage
instance Subst Predicate Value
instance Subst Predicate Arg
instance Subst Predicate ArgClass
instance Subst Predicate ArgName
instance Subst Predicate Predicate where
        isvar (PredicateVar x) = Just (SubstName x)
        isvar _ = Nothing

instance Alpha Equality
instance Alpha Predicate
instance Alpha Term
instance Alpha Proof
instance Alpha LogicalKind
instance Alpha Stage
instance Alpha Value
instance Alpha ArgClass
instance Alpha Arg
instance Alpha ArgName




{- Our temp main loop. -}
main = getContents >>= print . ottowa_parse . lexer
--main = getContents >>= print . lexer
}
