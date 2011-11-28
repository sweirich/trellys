{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeSynonymInstances  #-}


import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Subst(substR1)

data Stage = Plus | Minus deriving(Show)

data SuperKind = Logical Integer deriving (Show)


data LogicalKind = Formula Integer

         | QuasiForall ArgClass LogicalKind

  deriving(Show)

data Predicate = PredicateVar (Name Predicate)

           | PredicateLambda (Bind (ArgName, Embed ArgClass) Predicate)

           | PredicateApplication Predicate Arg

           | Forall (Bind (Name ArgName, Embed ArgClass) Predicate)



           -- | PredicateLetProof (Bind (Name Proof) Predicate) Proof

           -- | PredicateLetPredicate (Bind (Name Predicate) Predicate) Predicate

           -- | PredicateLetTerm (Bind (Name Term, Name Proof) Predicate) Term

           -- | Equal Term Term

           -- | Terminate Term

           -- | Disjunction Predicate Predicate

           -- | PredicateExist (Bind (Name Arg, Embed ArgClass) Predicate)

           -- | Bottom Integer

           -- | Order Term Term


  deriving(Show)

data Proof =  ProofVar (Name Proof)

             -- | InjectLeft Proof Predicate

             -- | InjectRight Proof Predicate

             -- | DisjunctionElimination (Bind (Name Proof) Proof) (Bind (Name Proof) Proof) Proof

             | ProofLambda (Bind (ArgName, Embed ArgClass) Proof)

             | ProofApplication Proof Arg

             -- | ExistentialIntroduction (Arg, Proof) Predicate

             -- | ProofLetProof (Bind (Name Proof) Proof) Proof

             -- | ProofLetPredicate (Bind (Name Predicate) Proof) Predicate

             -- | ProofLetTerm (Bind (Name Term, Name Proof) Proof) Term --Bind a term var and a proof var in a proof.

            -- | Join Term Term

--             | Pconv Proof [Q] [V] Need to ask question.

             -- | Valax Term

             -- | ProofOrder Term Term

         --  | Case
         --  | TCase

--             | Ind (Bind (Name Term, Name Proof, Embed Term, Name Proof) Proof)

--bind three variable in a proof

             -- | Contra Proof
             -- | Contraval Proof Proof


    deriving(Show)

data Term =  TermVar (Name Term)

           | Type Integer

           | Pi (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermLambda (Bind (ArgName, Embed Term) Term) Stage


          -- | TermLetTerm (Bind (Name Term, Name Proof) Term) Term

           -- | TermLetProof (Bind (Name Proof) Term) Proof

           -- | TermLetPredicate ((Bind (Name Predicate) Term)) Predicate



--           | Conv Term [] [] -- Troublesome, maybe later

--           | Case Term Variable Branches, maybe later


           -- | Tcast Term Proof

            | TermApplication Term Arg Stage


           -- | DataConstr String

           -- | Abort Term

           -- | Rec (Bind (Name Term, Name Term, Embed Term) Term)
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




         
         

$(derive [''Proof,''Term, ''Predicate, ''Arg, ''ArgName, ''Stage, ''Value, ''ArgClass, ''LogicalKind])

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


instance Subst Arg Stage
instance Subst Arg ArgName
instance Subst Arg ArgClass
instance Subst Arg LogicalKind
instance Subst Arg Predicate where
instance Subst Arg Term where
instance Subst Arg Arg where
instance Subst Arg Proof where


instance Subst Proof Arg
instance Subst Proof ArgName
instance Subst Proof Term where
  subst n p t = substR1 rep1 n p t 

instance Subst Proof Predicate where
  subst n t p = substR1 rep1 n t p 

instance Subst Proof Stage
instance Subst Proof LogicalKind
instance Subst Proof Value
instance Subst Proof ArgClass
instance Subst Proof Proof where
  isvar (ProofVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Term Arg
instance Subst Term ArgClass
instance Subst Term ArgName
instance Subst Term Proof where
  subst n t p = substR1 rep1 n t p 

instance Subst Term Predicate where
  subst n t p = substR1 rep1 n t p 

instance Subst Term LogicalKind
instance Subst Term Stage
instance Subst Term Value

instance Subst Term Term where
  isvar (TermVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Predicate Term where
  subst n pred tm = substR1 rep1 n pred tm 

instance Subst Predicate Proof where
  subst n pred prf = substR1 rep1 n pred prf 

instance Subst Predicate LogicalKind
instance Subst Predicate Stage
instance Subst Predicate Value
instance Subst Predicate Arg
instance Subst Predicate ArgClass
instance Subst Predicate ArgName

instance Subst Predicate Predicate where
        isvar (PredicateVar x) = Just (SubstName x)
        isvar _ = Nothing


instance Alpha Predicate
instance Alpha Term
instance Alpha Proof
instance Alpha LogicalKind
instance Alpha Stage
instance Alpha Value
instance Alpha ArgClass
instance Alpha Arg
instance Alpha ArgName

{- Building a complete test case for substitution:

0. For each substitution, test both bind variable(b) and unbind variable(a).
 
1. Show: [proof/proofvar]proof, [term/termvar]proof, [predicate/predicatevar]proof is working correctly.

2. Show [proof/proofvar]term, [term/termvar]term, [predicate/predicatevar]term is working correctly.

3. Show [proof/proofvar]predicate, [term/termvar]predicate, [predicate/predicatevar]predicate is working correctly.

4. Example: [yz/x](\x.x) , [yz/x](\z.x)
-}

