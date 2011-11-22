{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeSynonymInstances  #-}

module SubTest where

import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Subst(substR1)


-- | For this example, the only proposition is equality of programs.
data Pred = Equal Program Program
          deriving Show

data Proof = ProofLambda (Bind (Name Arg, Embed ArgClass) Proof) -- Proofs abstract over proofs or programs
           | ProofLambdaAN (Bind (ArgName, Embed ArgClass) Proof) -- This is the one we want to use, where we use ArgName, instead of Name Arg
           | ProofApp Proof Arg
           | ProofVar (Name Proof)
             -- ^ So we can embed programs in proofs -- join t1 t2 : t1 == t2
           | Join Program Program
             deriving Show

-- | Simplified programming language. Don't need abstraction/application to demonstrate the issue.
data Program = ProgVar (Name Program)
             | Type
               deriving Show

-- Lifting syntactic classes.

data ArgName = ANProof (Name Proof)
             | ANProg (Name Program) deriving Show

-- | An arg can be either a proof or a program.
data Arg = ArgProof Proof | ArgProg Program deriving Show

-- | The classifier for an argument can either be a predicate or a type (err... program)
data ArgClass = ArgClassPred | ArgClassType Program deriving Show


$(derive [''Pred, ''Proof, ''Program, ''ArgClass, ''Arg, ''ArgName])

-- | Boilerplate alpha instances
instance Alpha Pred
instance Alpha Proof
instance Alpha Program
instance Alpha ArgClass
instance Alpha Arg
instance Alpha ArgName


-- | Subst instances
instance Subst Proof Proof where
  isvar (ProofVar n) = Just (SubstName n)
  isvar _ = Nothing

instance Subst Arg Proof where
  subst n (ArgProof p) pf = subst (translate n) p pf
  subst n tm pf = substR1 rep1 n tm pf

instance Subst Proof Arg
instance Subst Proof ArgClass
instance Subst Proof Program
instance Subst Proof Pred

instance Subst Program Program where
  isvar (ProgVar n) = Just (SubstName n)
  isvar _ = Nothing

instance Subst Arg Program where
  subst n (ArgProg t) tm = subst (translate n) t tm
  subst n t t' = substR1 rep1 n t t'


instance Subst Program Proof
instance Subst Program ArgClass
instance Subst Program Arg
instance Subst Program Pred





instance Subst Arg Pred
instance Subst Arg ArgClass
instance Subst Arg Arg

instance Subst Proof ArgName
instance Subst Program ArgName
instance Subst Arg ArgName



x_prog,y_prog,z_prog :: Name Program
x_prog = string2Name "x_prog"
y_prog = string2Name "y_prog"
z_prog = string2Name "z_prog"

a_proof, b_proof :: Name Proof
a_proof = string2Name "a_proof"
b_proof = string2Name "b_proof"


-- | 'Type'
t1 = ProofLambda (bind (translate x_prog, ArgClassType Type) (Join (ProgVar x_prog) (ProgVar x_prog)))
t2 = ProofLambdaAN (bind (ANProg x_prog, ArgClassType Type) (Join (ProgVar x_prog) (ProgVar x_prog)))





