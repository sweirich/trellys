
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

| contr Proof                                       {Contra $2}

| valax Term                                        {Valax $2}


{
parseError :: [Token] -> a
parseError _ = error "Parse error"

data Logicdecl = Logicdecl String Predicate 
             deriving (Show)
  

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
             
           | DataType String

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


$(derive [''Proof,''Term, ''Predicate, ''Arg, ''ArgName, ''Equality, ''Stage, ''ArgClass, ''LogicalKind])

instance Subst LogicalKind Stage
instance Subst LogicalKind ArgName

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
instance Subst Term Term where
  isvar (TermVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Predicate Term 
instance Subst Predicate Proof
instance Subst Predicate Equality
instance Subst Predicate LogicalKind
instance Subst Predicate Stage
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
instance Alpha ArgClass
instance Alpha Arg
instance Alpha ArgName
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
instance Subst Term Term where
  isvar (TermVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Predicate Term 
instance Subst Predicate Proof
instance Subst Predicate Equality
instance Subst Predicate LogicalKind
instance Subst Predicate Stage
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
instance Alpha ArgClass
instance Alpha Arg
instance Alpha ArgName


data Token =

         TokenType

       | TokenData

       | TokenInt Integer

       | TokenWhere

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
lexer (':': cs) = 
		  let (cs1 : cs2) = cs in 
		   case cs1 of
		  ':' -> TokenDC : lexer cs2
		  '=' -> TokenDef : lexer cs2
		   _  -> TokenCL : lexer cs


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
      (var,rest)   -> let (x : xs) = var in 
                       case x of
          	       '$' -> TokenProofVar var : lexer rest
	               '&' -> TokenPredVar var : lexer rest
        	        _ -> TokenTermVar var : lexer rest


{- Our temp main loop. -}
main = getContents >>= print . sepcore-parser . lexer

}

