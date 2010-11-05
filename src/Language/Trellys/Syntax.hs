{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | This module captures the base abstract syntax of Trellys core. It
-- uses the generic locally nameless representation of binders from the
-- LangLib package.
module Language.Trellys.Syntax where

import Data.RepLib hiding (Arrow,Con)
import qualified Data.RepLib as RL

import Language.Trellys.GenericBind

import Text.ParserCombinators.Parsec.Pos

-- | Epsilon annotates whether an abstraction (resp. application) is implicit or
-- explicit.
data Epsilon = Runtime | Erased
               deriving (Eq,Show,Read)

-- | Theta annotates whether a term is classified "Logic" (total) or "Program"
-- (general). The constructor names should be
data Theta = Logic  -- ^ Proof terms
           | Program -- ^ Program terms
            deriving (Read,Show,Eq)

-- | Compute the least-upper bound on classifications.
lub :: Theta -> Theta -> Theta
lub Program _ = Program
lub _ Program = Program
lub x _ = x

instance Ord Theta where
  Logic <= Logic = True
  _ <= Program = True
  _ <= _ = False

(<:>) :: Name -> a -> (Name, Annot a)
x <:> t = (x, Annot t)


------------------------------
------------------------------
--- Annotated Language
------------------------------
------------------------------


-- The `Eq` instance for a `Bind`, found within Term, requires `Term`
-- be an instance of `Alpha`. This is the case, but it involves LangLib deriving
-- of a number of classes, which uses Template Haskell. If the deriving instance
-- (below) are declared in the `Term` definition, then we get a type error (No
-- instance for Alpha Term). The standalone deriving found below avoids the
-- problem.

deriving instance Show Term
deriving instance Eq Term


-- | The 'Term' representation is derived from the Ott language definition. In
-- the Trellys core, there is no distinction between types and terms. Moreover,
-- in contrast to the langauge definition, we do not draw a distinction between
-- names of datatypes and constructors introduced via datatype definitions (and
-- eliminated by case expressions) and variables introduced by lambda
-- abstractions and dependent products).
data Term = Var Name    -- | variables
          | Con Name   -- | term and type constructors
          | Type Int   -- | The 'Type' terminal
          -- | Functions: @\x.e@ and @\[x].e@
          -- No type annotations since we are bidirectional
          | Lam Epsilon (Bind Name Term)
          -- | Applications, tagged with stage
          | App Epsilon Term Term
          -- | A let expressoin
          | Let Theta Epsilon Term (Bind (Name, Name) Term)
          -- | Dependent functions: (x :^{th} A )_{ep} -> B
          | Arrow Theta Epsilon Term (Bind Name Term)
          -- | A case expression. The first 'Term' is the case scrutinee.
          | Case Term (Bind Name [Match])
          -- | The type of a proof that the two terms join, @a = b@
          | TyEq Term Term
          -- | The 'join' expression, written @join k1 k2@.  We 
          -- bidirectionally infer the terms
          | Join Int Int
          -- | @conv a by b at C@
          | Conv Term Term (Bind Name Term)
          -- | @contra a@ says @a@ is a contradiction and has any type
          | Contra Term
          -- | The @abort@ expression.
          | Abort
          -- | Recursive Definitions
          --  @recnat f x = body@ is represented as @(Bind (f,x) body)@
          | Rec Epsilon (Bind (Name, Name) Term)
          | NatRec Epsilon (Bind (Name, Name) Term)
          -- | Annotated terms
          | Ann Term Term
          -- | 'Paren' is for a parenthesized term, useful for pretty printing.
          | Paren Term
          -- | 'Pos' wraps a term with its source position.
          | Pos SourcePos Term

-- | A 'Match' is represents a case alternative. The first 'Name' is the
-- constructor name, the rest of the 'Name's are pattern variables
type Match = (Name, Bind [(Name, Epsilon)] Term)


-- | This just deletes any top level Pos or Paren constructors from a term
delPosParen :: Term -> Term
delPosParen (Pos _ tm) = tm
delPosParen (Paren tm) = tm
delPosParen tm         = tm
  


-- | A Module has a name, a list of imports, and a list of declarations
data Module = Module { moduleName :: Name,
                       moduleImports :: [ModuleImport],
                       moduleEntries :: [Decl]
                     }
            deriving (Show,Eq)

-- | A ModuleImport is just a name (for now).
newtype ModuleImport = ModuleImport Name
            deriving (Show,Eq)

data Decl = Sig Name Theta Term
          | Def Name Term
          | Data Name Telescope Theta Int [Constructor]
          | AbsData Name Telescope Theta Int
  deriving (Show,Eq)


-- | A Constructor has a name and a type
type Constructor = (Name,Term)

-------------
-- Telescopes
-------------
-- | This definition of 'Telescope' should be replaced by the one from LangLib.
type Telescope = [(Name,Term,Theta,Epsilon)]

-- | teleApp applies some term to all the variables in a telescope
teleApp :: Term -> Telescope -> Term
teleApp tm tms =
  foldl (\a (nm,_,_,ep) -> App ep a (Var nm)) tm tms

telePi :: Telescope -> Term -> Term
telePi tele tyB =
  foldr (\(n,tm,th,ep) ret -> Arrow th ep tm (bind n ret))
        tyB tele

domTeleMinus :: Telescope -> [Name]
domTeleMinus tele =
  map (\(n,_,_,_) -> n) $ filter (\(_,_,_,ep) -> ep == Erased) tele

teleVars :: Telescope -> [Name]
teleVars = map (\(v,_,_,_) -> v)

-- FIXME horribly inefficient.
swapTeleVars :: Telescope -> [Name] -> Telescope
swapTeleVars [] [] = []
swapTeleVars ((v,a,th,ep):tele) (v':vs) =
  (v',a,th,ep):(subst v (Var v') $ swapTeleVars tele vs)
swapTeleVars _ _ = 
  error "Internal error: lengths don't match in swapTeleVars"

-- (changeStage args tele) changes the stage annotation of each term 
-- in args to be the one given by the corresponding element of tele.
-- This assumes the lists are the same length.
changeStage :: [(Term,Epsilon)] -> Telescope -> [(Term,Epsilon)]
changeStage [] [] = []
changeStage ((t,_):args) ((_,_,_,ep):tele) = (t,ep):(changeStage args tele)
changeStage _ _ = 
  error "Internal error: lengths don't match in changeStage"

--------------
-- Basic query and manipulation functions on annotated terms
--------------
isVar :: Term -> Maybe Name
isVar (Pos _ t) = isVar t
isVar (Paren t) = isVar t
isVar (Var n)   = Just n
isVar _         = Nothing

isCon :: Term -> Maybe Name
isCon (Pos _ t) = isCon t
isCon (Paren t) = isCon t
isCon (Con n)   = Just n
isCon _         = Nothing


isType :: Term -> Maybe Int
isType (Pos _ t)  = isType t
isType (Paren t)  = isType t
isType (Type n)   = Just n
isType _          = Nothing

isTyEq :: Term -> Maybe (Term, Term)
isTyEq (Pos _ t) = isTyEq t
isTyEq (Paren t) = isTyEq  t
isTyEq (TyEq ty0 ty1) = Just (ty0,ty1)
isTyEq _ = Nothing

isArrow :: Term -> Maybe (Theta, Epsilon, Term, Bind Name Term)
isArrow (Pos _ t)            = isArrow t
isArrow (Paren t)            = isArrow t
isArrow (Arrow th ep tm bnd) = Just (th,ep,tm,bnd)
isArrow _                    = Nothing

-- splitApp makes sure a term is an application and returns the
-- two pieces
splitApp :: Term -> (Term, [(Term,Epsilon)])
splitApp e = splitApp' e []
  where
    splitApp' (App ep t0 t1) acc = splitApp' t0 ((t1,ep):acc)
    splitApp' (Paren tm) acc = splitApp' tm acc
    splitApp' (Pos _ tm) acc = splitApp' tm acc
    splitApp' t acc = (t, acc)

multiApp :: Term -> [(Term,Epsilon)] -> Term
multiApp = foldl (\tm1 (tm2,ep) -> App ep tm1 tm2)

-- splitPi pulls apart a dependent product returning all the arguments and
-- the final return type
splitPi :: (HasNext m, Fresh m) => Term -> m (Telescope,Term)
splitPi tm = splitPi' tm []
  where
    splitPi' (Pos _ tm')          acc = splitPi' tm' acc
    splitPi' (Paren tm')          acc = splitPi' tm' acc
    splitPi' (Arrow th ep tmA bd) acc =
      do (nm,tmB) <- unbind bd
         splitPi' tmB ((nm,tmA,th,ep):acc)
    splitPi' tm'                  acc = return (reverse acc, tm')




------------------------
------------------------
--- Unannotated Language
------------------------
------------------------

deriving instance Show ETerm
deriving instance Eq ETerm


-- ETerm for "erased" term
data ETerm = EVar Name
           | ECon Name
           | EType Int
           | EArrow Theta Epsilon ETerm (Bind Name ETerm)
           | ELam (Bind Name ETerm)
           | EApp ETerm ETerm
           | ETyEq ETerm ETerm
           | EJoin
           | EAbort
           | ERecPlus (Bind (Name, Name) ETerm)
           | ERecMinus (Bind Name ETerm)
           | ECase ETerm [EMatch]
           | ELet ETerm (Bind Name ETerm)
           | EContra

type EMatch = (Name, Bind [Name] ETerm)

isEVar :: ETerm -> Maybe Name
isEVar (EVar n)   = Just n
isEVar _          = Nothing

isECon :: ETerm -> Maybe Name
isECon (ECon n)   = Just n
isECon _          = Nothing

-- splitEApp makes sure a term is an application and returns the
-- two pieces
splitEApp :: ETerm -> (ETerm, [ETerm])
splitEApp e = splitEApp' e []
  where
    splitEApp' (EApp t0 t1) acc = splitEApp' t0 ((t1):acc)
    splitEApp' t acc = (t, acc)

--------------------
-- LangLib instances
--------------------  

$(derive [''Epsilon, ''Theta, ''Term, ''ETerm])


instance Alpha Term where
  match' pol  (Pos _ t1) t2 = match' pol t1 t2
  match' pol  t1 (Pos _ t2) = match' pol t1 t2
  match' pol (Paren t1) t2 = match' pol t1 t2
  match' pol t1 (Paren t2) = match' pol t1 t2
  match' pol t1 t2 = matchR1 rep1 pol t1 t2

instance Alpha Theta
instance Alpha Epsilon

instance Subst Term Term where
  isvar (Var m) = Just (m,id)
  isvar _ = Nothing
instance Subst Term Epsilon
instance Subst Term Theta


instance Alpha ETerm
instance Subst ETerm ETerm where
  isvar (EVar m) = Just (m,id)
  isvar _ = Nothing
instance Subst ETerm Epsilon
instance Subst ETerm Theta

-- -- Why do you need these instances?
instance Subst Name Theta
instance Subst Name Epsilon
instance Subst Name Term where
  isvar (Var m) = Just (m, Var)
  isvar _ = Nothing
instance Subst Name ETerm

{-
instance Pattern Telescope
instance Pattern Term
instance Pattern Theta
instance Pattern Position
instance Pattern Epsilon
instance Pattern (Maybe Name)

-}


