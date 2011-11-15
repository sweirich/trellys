{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeSynonymInstances  #-}

import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)

data Stage = Plus | Minus deriving(Show)

data SuperKind = Logical Integer deriving (Show)

data ArgClass = ArgClassTerm Term

              | ArgClassPredicate Predicate

              | ArgClassLogicalKind LogicalKind

     deriving(Show)

data Arg = ArgTerm Term

         | ArgProof Proof

         | ArgPredicate Predicate

       deriving(Show)

data LogicalKind = Formula Integer

         | LogicalKindForall  ArgClass LogicalKind

  deriving(Show)

data Predicate = PredicateVar(Name Predicate)

           | PredicateLambda (Bind (Name Arg, Embed ArgClass) Predicate)

           | PredicateApplication Predicate Arg

           | PredicateForall (Bind (Name Arg, Embed ArgClass) Predicate)

--           | PredicateLetProof (Bind (Name Arg) Predicate) Proof

  --         | PredicateLetPredicate (Bind (Name Predicate) Predicate) Predicate

    --       | PredicateLetTerm (Bind (Name Term, Name Proof) Predicate) Term

           | Equal Term Term

           | Terminate Term

           | Disjunction Predicate Predicate

           | PredicateExist (Bind (Name Arg, Embed ArgClass) Predicate)

           | Bottom Integer

           | Order Term Term


  deriving(Show)

data Proof =  ProofVar (Name Proof)

             | InjectLeft Proof Predicate

             | InjectRight Proof Predicate

           -- | DisjunctionElimination (Bind (Name Proof) Proof) (Bind (Name Proof) Proof) Proof

             | ProofLambda (Bind (Name Arg, Embed ArgClass) Proof)

             | ProofApplication Proof Arg

             | ExistentialIntroduction (Arg, Proof) Predicate

--             | ProofLetProof (Bind (Name Proof) Proof) Proof

         --    | ProofLetPredicate (Bind (Name Predicate) Proof) Predicate

          --   | ProofLetTerm (Bind (Name Term, Name Proof) Proof) Term --Bind a term var and a proof var in a proof.

             | Join Term Term

--             | Pconv Proof [Q] [V] Need to ask question.

             | Valax Term

             | ProofOrder Term Term

         --  | Case
         --  | TCase

         --  | Ind (Bind (Name Term, Name Proof, Embed Term, Name Proof) Proof)

--bind three variable to a proof

             | Contra Proof
             | Contraval Proof Proof


    deriving(Show)

data Term = TermVar (Name Term)

           | Type Integer

           | Pi (Bind (Name Arg, Embed ArgClass) Term) Stage

           | TermLambda (Bind (Name Arg, Embed ArgClass) Term) Stage

  --         | TermLetTerm (Bind (Name Term, Name Proof) Term) Term

    --       | TermLetProof (Bind (Name Proof) Term) Proof

      --     | TermLetPredicate ((Bind (Name Predicate) Term)) Predicate



--           | Conv Term [] [] -- Troublesome, maybe later

--           | Case Term Variable Branches, maybe later


           | Tcast Term Proof

           | TermApplication Term Arg Stage

           | DataConstr String

           | Abort Term

     --      | Rec (Bind (Name Term, Name Term, Embed Term) Term)

  deriving(Show)


data Value = Value | NonValue deriving (Show)
type TypingContext = [(Name Arg, ArgClass, Value)]


$(derive [''Proof,''Term, ''Predicate, ''LogicalKind, ''Stage, ''SuperKind, ''Value, ''Arg, ''ArgClass])


instance Subst LogicalKind Stage
instance Subst LogicalKind Value
instance Subst LogicalKind Arg
instance Subst LogicalKind ArgClass
instance Subst LogicalKind Predicate
instance Subst LogicalKind Term
instance Subst LogicalKind Proof
instance Subst LogicalKind LogicalKind


instance Subst Arg Stage
instance Subst Arg ArgClass
instance Subst Arg LogicalKind

instance Subst Arg Predicate where
   subst n arg pred = case subst n arg (ArgPredicate pred) of
                         ArgPredicate p -> p
                         _ -> error "Subst Arg Pred"


instance Subst Arg Term where
   subst n arg term = case subst n arg (ArgTerm term) of
                         ArgTerm p -> p
                         _ -> error "Subst Arg Term"


instance Subst Arg Arg where
    subst n (ArgProof p) t = subst (translate n) p t
    subst n (ArgPredicate p) t = subst (translate n) p t
    subst n (ArgTerm p) t = subst (translate n) p t



   -- subst n (ArgProof p) t = subst (translate n) p t
   -- subst n (ArgPredicate p) t = subst (translate n) p t
   -- subst n (ArgTerm p) t = subst (translate n) p t


instance Subst Arg Proof where
   subst n arg proof = case subst n arg (ArgProof proof) of
                         ArgProof p -> p
                         _ -> error "Subst Arg Proof"





instance Subst Proof Arg
instance Subst Proof Term
instance Subst Proof Predicate
instance Subst Proof Stage
instance Subst Proof LogicalKind
instance Subst Proof Value
instance Subst Proof ArgClass
instance Subst Proof Proof where
  isvar (ProofVar x) = Just (SubstName x)
  isvar _ = Nothing



instance Subst Term Arg
instance  Subst Term ArgClass
instance Subst Term Proof
instance Subst Term Predicate
instance Subst Term LogicalKind
instance Subst Term Stage
instance Subst Term Value
instance Subst Term Term where
  isvar (TermVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Predicate Term
instance Subst Predicate Proof
instance Subst Predicate LogicalKind
instance Subst Predicate Stage
instance Subst Predicate Value
instance Subst Predicate Arg
instance Subst Predicate ArgClass
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

nx :: Name Proof
nx = string2Name "x"

x :: Proof
x = (ProofVar nx)

y :: Arg
y = ArgProof (ProofVar (string2Name "y"))

test = subst (translate nx) y x
--            Name Arg      Arg Proof


nz :: Name Term
nz = string2Name "z"

z :: Term
z = (TermVar nz)

t :: Term
t = TermLambda ( bind ( (translate nz), Embed (ArgClassTerm z))  z) Plus


u :: Proof
u = ProofLambda (bind ((translate nz), Embed (ArgClassTerm z)) (Join z z))

test2 = subst (translate nx) (ArgTerm t) x
-- [t/x]x should give me t but it gives me x


test3 = subst (translate nz) (ArgTerm t) u

