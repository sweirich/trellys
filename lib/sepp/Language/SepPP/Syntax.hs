{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances  #-}
module Language.SepPP.Syntax (
  Decl(..),Module(..),Term(..),
  Stage(..),Kind(..),Alt,
  TName, ModName,
  ETerm(..), erase, erasedValue,
  down,
  splitApp, splitApp', isStrictContext, var, app) where

import Unbound.LocallyNameless hiding (Con)
import Unbound.LocallyNameless.Alpha(aeqR1)
import Text.Parsec.Pos
import Control.Monad(mplus)
import Control.Applicative((<$>), (<*>))

import Data.Typeable

-- | 'Unbound' Name representation
type TName = Name Term

-- | A module is just a list of definitions.
type ModName = Name Module
data Module = Module ModName [Decl] deriving (Show)

-- Name, type, value
data Decl =  ProgDecl TName Term Term
          |  ProofDecl TName Term Term
          | DataDecl Term Term [(TName,Term)]
          | AxiomDecl TName Term
     deriving Show

data Stage = Dynamic | Static deriving (Eq,Show)
data Kind = Form | Program deriving (Eq,Show)
-- | The representation of SepPP expressions.

data Term = Var TName                                 -- Term, Proof
          | Con TName                                 -- Term
          | Formula Integer                           -- LogicalKind
          | Type                                      -- Term
            -- |
          | Pi Stage (Bind (TName, Embed Term) Term)  -- Term
          | Forall (Bind (TName, Embed Term) Term)    -- Predicate

            -- We keep a stage annotation around so that we can erase an
            -- application without knowing its type.
          | App Term Stage Term                       -- Predicate, Proof, Term
          | Lambda Kind Stage (Bind (TName, Embed Term) Term)  -- Predicate, Proof, Term

            -- There are actually two types of case expressions in the design
            -- document. We combine these two, with the extra termination proof
            -- argument wrapped in Maybe.

          | Case Term (Maybe Term) (Bind TName [Alt])       -- Proof, Term


          | TerminationCase Term (Bind TName (Term,Term))    -- Proof


          | Join Integer Integer                      -- Proof
                                                      -- intros a
          | Equal Term Term                           -- Predicate

          | Val Term                                  -- Proof
                                                      -- intros a
          | Terminates Term                           -- Predicate

          -- Contra is used when you have an equation between
          -- distinct constructors.
          | Contra Term                               -- Proof
          -- Contraabort is used when you have an proof that t = abort
          -- and a proof that t terminates.
          | ContraAbort Term Term                     -- Proof

          -- The term argument is the type you wish to ascribe
          | Abort Term                                -- Term


          -- The bool associated with the equality proof is whether or not the
          -- type occurs in an erased position. If it does, then the term should
          -- be an equality proof. If it doesn't then the term should be some
          -- value with the a type that is an equality proof.
          | Conv Term [Term] (Bind [TName] Term)  -- Proof, Term
          | ConvCtx Term Term -- Simple quote style contexts


          -- For inductive proofs we have an ordering. The argument is the
          -- witness to the equality that demonstrates the equality.
          | Ord Term                                  -- Proof
                                                      -- intros a
          | IndLT Term Term                           -- Pred
          | OrdTrans Term Term


          | Ind (Bind (TName, (TName, Embed Term), TName) Term) -- proof
          | Rec (Bind (TName, (TName, Embed Term)) Term) -- term

          -- In a conversion context, the 'Escape' term splices in an equality
          -- proof (or an expression that generates an equality proof).
          | Escape Term

          | Let (Bind (TName,TName,Embed Term) Term)

          | Aborts Term
          | Sym Term -- Should be a derived form
          | Refl -- Should be a derived form
          | Trans Term Term -- Should be a derived form
          | MoreJoin [Term] -- Should be a derived form

          | Ann Term Term  -- Predicate, Proof, Term (sort of meta)
          | Pos SourcePos Term
          deriving (Show,Typeable)


---------------------------------------------------------

type Alt = Bind (String, [TName]) Term
$(derive_abstract [''SourcePos])
instance Alpha SourcePos

$(derive [''Term, ''Module, ''Decl, ''Stage, ''Kind])


instance Alpha Term where
  aeq' c (Pos _ t1) t2 = t1 `aeq` t2
  aeq' c t1 (Pos _ t2) = t1 `aeq` t2
  aeq' c t1 t2 = aeqR1 rep1 c t1 t2

instance Alpha Module
instance Alpha Decl
instance Alpha Stage
instance Alpha Kind
instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Term Stage
instance Subst Term Kind
instance Subst Term SourcePos



splitApp (App t0 _ t1) = splitApp' t0 [t1]
  where splitApp' (App s0 _ s1) acc = splitApp' s0 (s1:acc)
        splitApp' (Pos _ t) acc = splitApp' t acc
        splitApp' s acc = s:(reverse acc)
splitApp (Pos _ t) = splitApp t
splitApp t = []


splitApp' t = case splitApp t of
                [] -> (t,[])
                (x:xs) -> (x,xs)

isStrictContext (Pos _ t) = isStrictContext t
isStrictContext (Escape e) = Just (e,id)
isStrictContext (App e1 stage e2) =
 case isStrictContext e1 of
   Just (e,k1) -> Just (e,\v -> App (k1 v) stage e2)
   Nothing ->  case isStrictContext e2 of
                 Just (e,k2) -> Just (e,\v -> App e1 stage (k2 v))
                 Nothing -> Nothing


isStrictContext (Case e term bs) = case isStrictContext e of
                               Just (e',k) -> Just (e',\v -> Case (k v) term bs)


isStrictContext _ = Nothing

var s = Var (string2Name s)
app f x = App f Dynamic x



down (Pos _ t) = down t
down t = t



-- | Erased Terms
type EName = Name ETerm
data ETerm = EVar (Name ETerm)
           | ECon (Name ETerm)
           | EApp ETerm ETerm
           | ELambda (Bind EName ETerm)
           | ERec (Bind (EName, EName) ETerm)
           | ECase ETerm [Bind (String,[EName]) ETerm]
           | ELet (Bind (EName, Embed ETerm) ETerm)
           | EType
  deriving (Show)

erase (Pos _ t) = erase t
erase Type = return EType
erase (Var n) = return $ EVar (translate n)
erase (Con n) = return $ ECon (translate n)
erase (App f Static _) = erase f
erase (App f Dynamic x) = EApp <$> (erase f) <*> (erase x)
erase (Lambda _ Static binding) = do
  (_,body) <- unbind binding
  erase body
erase (Lambda _ Dynamic binding) = do
  ((n,_),body) <- unbind binding
  ELambda <$> ((bind (translate n)) <$> erase body)
erase (Rec binding) = do
  ((n,(arg,_)),body) <- unbind binding
  ERec <$> (bind (translate n, translate arg)) <$> erase body
erase (Case scrutinee _ binding) = do
    (_,alts) <- unbind binding
    ECase <$> erase scrutinee <*> mapM eraseAlt alts
  where eraseAlt binding = do
          ((c,vs),body) <- unbind binding
          bind (c,map translate vs) <$> erase body

erase (Let binding) = do
    ((x,_,Embed t),body) <- unbind binding
    et <- erase t
    ebody <- erase body
    return $ ELet (bind (translate x,Embed et) ebody)




erase (Ann t _) = erase t
erase t =  do
  fail $  "The erasure function is not defined on: " ++ show t

erasedValue (ECase _ _) = False
erasedValue (EApp _ _) = False
erasedValue (ELet _) = False
erasedValue _ = True




$(derive [''ETerm])

instance Alpha ETerm
instance Subst ETerm ETerm where
  isvar (EVar x) = Just (SubstName x)
  isvar _ = Nothing
