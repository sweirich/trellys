{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeSynonymInstances  #-}

module Language.SepCore.Syntax(
     Logicdecl(..), Stage(..), SuperKind(..),
     LogicalKind(..), Predicate(..), Proof(..),
     Term(..), Arg(..), ArgName(..), ArgClass(..),
     Value(..), Equality(..), TypingContext, Proofdef(..),
     Progdecl(..), Progdef(..), Preddecl(..), Preddef(..), Datatypedecl(..), Declaration(..),Module(..), TermScheme(..)
     
                               ) where 

import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)

import Unbound.LocallyNameless.Subst(substR1)

type Module = [Declaration] 

data Declaration = DeclLogic Logicdecl
                 | DeclProof Proofdef
                 | DeclProgdecl Progdecl           
                 | DeclProgdef Progdef
                 | DeclPreddef Preddef
                 | DeclPreddecl Preddecl
                 | DeclData Datatypedecl
                   deriving(Show)

data Logicdecl = Logicdecl Proof Predicate 
             deriving (Show)

data Proofdef = Proofdef Proof Proof 
             deriving (Show)

data Progdecl = Progdecl Term Term
             deriving(Show)

data Progdef = Progdef Term Term
             deriving(Show)

data Preddecl = Preddecl Predicate LogicalKind
             deriving(Show)

data Preddef = Preddef Predicate Predicate
             deriving(Show)

data Datatypedecl = Datatypedecl Term Term [(Term, Term)]
             deriving(Show)


      
data Stage = Plus | Minus deriving(Show)

data SuperKind = Logical Integer deriving (Show)

data LogicalKind = Formula Integer

         | QuasiForall (Bind (ArgName, Embed ArgClass) LogicalKind)

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

type TermScheme = [Term]

-- type TermBranches = [Bind TermScheme Term]

type TermBranches = [(TermScheme,Term)]

data Equality = Equality Predicate
            
              | EqualityProof Proof

    deriving(Show)    

data Term =  TermVar (Name Term)

           | Type Integer

           | Pi (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermLambda (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermLetTerm (Bind (Name Term, Name Proof) Term) Term
           
           | TermLetTerm1 (Bind (Name Term) Term) Term
             
           | TermLetProof (Bind (Name Proof) Term) Proof

           | TermLetPredicate ((Bind (Name Predicate) Term)) Predicate

           | ConvTerm Term [Equality] (Bind [(Name Term)] Term)

           | TermCase Term (Bind (Name Term)  [(Term, [ArgName],Term)])

           | TermCase1 Term TermBranches

           | Tcast Term Proof

           | TermApplication Term Arg Stage

           | DataConstr String
             
           | DataType String

           | Abort Term

           | Rec (Bind (Name Term, Name Term, Embed Term) Term)
           
           | Undefined
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

         deriving (Show, Eq, Ord)


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

{- Building a small-scale test case for substitution:
 
1. Show: [proof/proofvar]proof is working correctly.

2. Show: [term/termvar]term  is working correctly.

3. Show: [predicate/predicatevar]predicate is working correctly.

4. Show: [arg/argname]proof is working correctly.

5. Show: [term/termvar]predicate is working correctly.

6. Example: [yz/x](\z.zx)
-}

x_term, y_term, z_term, u_term :: Name Term 

x_proof, y_proof, z_proof :: Name Proof 

x_pred, y_pred, z_pred :: Name Predicate

x_term = string2Name "x_term"
y_term = string2Name "y_term"
z_term = string2Name "z_term"
u_term = string2Name "u_term"
x_proof = string2Name "x_proof"
y_proof = string2Name "y_proof"
z_proof = string2Name "z_proof"
x_pred = string2Name "x_pred"
y_pred = string2Name "y_pred"
z_pred = string2Name "z_pred"

--1. Test Case for [proof/proofvar]proof:

-- \z:Z.zx a proof
plzZzx = ProofLambda (bind (ArgNameProof z_proof, (Embed (ArgClassPredicate (PredicateVar z_pred)))) (ProofApplication (ProofVar z_proof) (ArgProof (ProofVar x_proof)))) 

-- yz a proof
pyz = ProofApplication (ProofVar y_proof) (ArgProof (ProofVar z_proof))

-- [yz/x](\z:Z.zx)=\z:Z.z(yz')
test1 = subst x_proof pyz plzZzx

--2. Test Case for [term/termvar]term

--yz is term
tyz = TermApplication (TermVar y_term) (ArgTerm (TermVar z_term)) Plus

-- \z:Y.zx is a term
tlzYzx = TermLambda (bind (ArgNameTerm z_term, (Embed (ArgClassTerm (TermVar y_term)))) (TermApplication (TermVar z_term) (ArgTerm (TermVar x_term)) Plus)) Plus 

-- [yz/x](\z:Z.zx)=\z:Z.z(yz')
test2 = subst x_term tyz tlzYzx

--3. Test Case for [pred/predvar]pred

--yz is pred
pdyz = PredicateApplication (PredicateVar y_pred) (ArgPredicate (PredicateVar z_pred)) 

-- \z:F0.zx is a pred
pdlzF0zx = PredicateLambda (bind (ArgNamePredicate z_pred, (Embed (ArgClassLogicalKind (Formula 0)))) (PredicateApplication (PredicateVar z_pred) (ArgPredicate (PredicateVar x_pred)))) 

--[yz/x]\z:F0.zx=\z:F0.z(yz')
test3 = subst x_pred pdyz pdlzF0zx

--4. Test Case for [arg/argname]proof

--yz is term being promoted to arg 
atyz = ArgTerm (TermApplication (TermVar y_term) (ArgTerm (TermVar z_term)) Plus)

-- \z:U.zx is a proof, but x is termvar
plzUxz = ProofLambda (bind (ArgNameProof z_proof, (Embed (ArgClassPredicate (PredicateVar y_pred)))) (ProofApplication (ProofVar z_proof) (ArgTerm (TermVar x_term)))) 

-- [yz/x](\z:U.zx)=\z:U.z(yz')
test4 = subst (translate x_term) atyz plzUxz

-- 5. Test case for [term/termvar]pred

-- tyz is term


-- \z:Z.zx is a pred, but x is a termvar

pdlzZxz = PredicateLambda (bind (ArgNamePredicate z_pred, (Embed (ArgClassLogicalKind (Formula 0)))) (PredicateApplication (PredicateVar z_pred) (ArgTerm (TermVar x_term)))) 

--[yz/z]\z:U.zx= \z:U.z(yz')
test5 = subst x_term tyz pdlzZxz

