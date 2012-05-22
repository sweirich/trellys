{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | This module captures the base abstract syntax of Trellys core. It
-- uses the generic locally nameless representation of binders from the
-- LangLib package.
module Language.Trellys.Syntax where

import Generics.RepLib hiding (Arrow,Con)
import qualified Generics.RepLib as RL

import Language.Trellys.GenericBind

import Text.ParserCombinators.Parsec.Pos
import Data.Maybe (fromMaybe)

type TName = Name Term
type EName = Name ETerm
-- really "Name Module", but since we never substitute for these,
-- this definition saves defining some typeclass instances:
type MName = Name ()

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

-- (<:>) :: TName -> a -> (TName, Annot a)
-- x <:> t = (x, Annot t)


------------------------------
------------------------------
--- Source Language
------------------------------
------------------------------

deriving instance Show Term

-- | The 'Term' representation is derived from the Ott language definition. In
-- the Trellys core, there is no distinction between types and terms. Moreover, in contrast to the langauge definition, we do not draw a distinction between
-- names of datatypes and constructors introduced via datatype definitions (and
-- eliminated by case expressions) and variables introduced by lambda
-- abstractions and dependent products).
data Term = Var TName    -- | variables
          | Con TName [(Term,Epsilon)]   -- | term and type constructors (fully applied)
          | Type Integer   -- | The 'Type' terminal
          -- | Functions: @\x.e@ and @\[x].e@
          -- No type annotations since we are bidirectional
          | Lam Epsilon (Bind TName Term)
          -- | Applications, tagged with stage
          | App Epsilon Term Term
          -- | A let expression (bound name, equality name, value)
          | Let Theta Epsilon (Bind (TName, TName, Embed Term) Term)
          -- | Dependent functions: (x : A )_{ep} -> B
          | Arrow  Epsilon (Bind (TName, Embed Term) Term)
          -- | A case expression. The first 'Term' is the case scrutinee.
          | Case Term (Bind TName [Match])
          -- | The heterogenous structural order type, @a < b@
          | Smaller Term Term
          -- | Constructor for the structural order, @ord a@
          | OrdAx Term 
          -- | Proof term for transitivity of the structural order, @ord a1 a2@.
          | OrdTrans Term Term
          -- | The type of a proof that the two terms join, @a = b@
          | TyEq Term Term
          -- | The 'join' expression, written @join k1 k2@.  We
          -- bidirectionally infer the terms
          | Join Int Int
          -- | @conv a by b at C@
          | Conv Term [(Bool,Term)] (Bind [TName] Term)
          -- | @contra a@ says @a@ is a contradiction and has any type
          | Contra Term
          -- | The @abort@ expression.
          | Abort
          -- | Recursive Definitions
          --  @ind f x = body@ is represented as @(Bind (f,x) body)@
          | Rec Epsilon (Bind (TName, TName) Term)
          | Ind Epsilon (Bind (TName, TName) Term)
          -- | Annotated terms
          | Ann Term Term
          -- | 'Paren' is for a parenthesized term, useful for pretty printing.
          | Paren Term
          -- | 'Pos' wraps a term with its source position.
          | Pos SourcePos Term
          -- | Internalized Typing Judgement
          | At Term Theta
          -- | Termination case
          | TerminationCase Term (Bind TName (Term, (Bind TName Term)))    -- Proof
          -- | Derived form: assertion that t1 of type t2 terminates
          | TrustMe 
          -- | The TRUSTME form.
          | InferMe
          -- | Concrete syntax is an underscore.

          
-- | A 'Match' represents a case alternative. The first 'TName' is the
-- constructor name, the rest of the 'TName's are pattern variables
type Match = (TName, Bind [(TName, Epsilon)] Term)

-- | This just deletes any top level Pos or Paren constructors from a term
delPosParen :: Term -> Term
delPosParen (Pos _ tm) = tm
delPosParen (Paren tm) = tm
delPosParen tm         = tm

-- delPosParenDeep :: Term -> Term
delPosParenDeep :: Rep a => a -> a
delPosParenDeep = everywhere (mkT delPosParen)

-- | Partial inverse of Pos
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _         = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: Term -> Maybe SourcePos
unPosDeep = something (mkQ Nothing unPos)

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term -> SourcePos
unPosFlaky t = fromMaybe (newPos "unknown location" 0 0) (unPosDeep t)

-- | A Module has a name, a list of imports, and a list of declarations
data Module = Module { moduleName :: MName,
                       moduleImports :: [ModuleImport],
                       moduleEntries :: [Decl]
                     }
            deriving (Show)

-- | A ModuleImport is just a name (for now).
newtype ModuleImport = ModuleImport MName
            deriving (Show,Eq)

data Decl = Sig  TName Theta Term
          | Axiom TName Theta Term
          | Def TName Term
          | Data TName Telescope Theta Integer [ConstructorDef]
          | AbsData TName Telescope Theta Integer
  deriving (Show)


-- | A Constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos TName Telescope
  deriving (Show)

-- | Goals (in the Coq sense), just used for pretty-printing so far.
data Goal = Goal [Decl] --available context
                 Term   --type to be proven.

-------------
-- Telescopes
-------------
-- | This definition of 'Telescope' should be replaced by the one from LangLib.
type Telescope = [(TName,Term,Epsilon)]

-- | teleApp applies some term to all the variables in a telescope
teleApp :: Term -> Telescope -> Term
teleApp tm tms =
  foldl (\a (nm,_,ep) -> App ep a (Var nm)) tm tms

telePi :: Telescope -> Term -> Term
telePi tele tyB =
  foldr (\(n,tm,ep) ret -> Arrow ep (bind (n,embed tm) ret))
        tyB tele

domTele :: Telescope -> [TName]
domTele = map (\(v,_,_) -> v)

domTeleMinus :: Telescope -> [TName]
domTeleMinus tele =
  [n | (n,_,ep) <- tele, ep == Erased]

swapTeleVars :: Telescope -> [TName] -> Telescope
swapTeleVars [] [] = []
swapTeleVars ((v,a,ep):tele) (v':vs) =
  (v',a,ep):(subst v (Var v') $ swapTeleVars tele vs)
swapTeleVars _ _ =
  error "Internal error: lengths don't match in swapTeleVars"

setTeleEps :: Epsilon -> Telescope -> Telescope
setTeleEps ep = map (\(x,ty,_) -> (x,ty,ep))

--------------
-- Basic query and manipulation functions on source terms
--------------
isVar :: Term -> Maybe TName
isVar (Pos _ t) = isVar t
isVar (Paren t) = isVar t
isVar (Var n)   = Just n
isVar _         = Nothing

isType :: Term -> Maybe Integer
isType (Pos _ t)  = isType t
isType (Paren t)  = isType t
isType (Type n)   = Just n
isType _          = Nothing

isTyEq :: Term -> Maybe (Term, Term)
isTyEq (Pos _ t) = isTyEq t
isTyEq (Paren t) = isTyEq  t
isTyEq (TyEq ty0 ty1) = Just (delPosParenDeep ty0, delPosParenDeep ty1)
isTyEq _ = Nothing

isSmaller :: Term -> Maybe (Term, Term)
isSmaller (Pos _ t) = isSmaller t
isSmaller (Paren t) = isSmaller t
isSmaller (Smaller a b) = Just (delPosParenDeep a, delPosParenDeep b)
isSmaller _ = Nothing 

isArrow :: Term -> Maybe (Epsilon, Bind (TName, Embed Term) Term)
isArrow (Pos _ t)      = isArrow t
isArrow (Paren t)      = isArrow t
isArrow (Arrow ep bnd) = Just (ep,bnd)
isArrow _              = Nothing

isAt :: Term -> Maybe (Term, Theta)
isAt (Pos _ t) = isAt t
isAt (Paren t) = isAt t
isAt (At t th) = Just (t, th)
isAt _         = Nothing

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

---------------------------------------
---------------------------------------
-- Annotated Core Language
---------------------------------------
---------------------------------------

type AName = Name ATerm

deriving instance Show ATerm

-- | ATerm are annotated terms.
--   Given an environment and a theta, we can synthesize an unannotated term and a type.

data ATerm = 
    AVar AName
  | AFO ATerm
  | ASquash ATerm
  | ACumul ATerm Integer
  | AType Integer
  | AUnboxVar Theta ATerm    --the theta is the what we should check the inner term at.
  | ATCon AName [ATerm]
  | ADCon AName [ATerm] [(ATerm,Epsilon)]
  -- ET_arrow and ET_arrowImpred
  | AArrow   Epsilon (Bind (AName, Embed ATerm) ATerm)
  -- ET_lamPlus and ET_lamMinus. The first ATerm is they (pi) type of the entire lambda.
  | ALam ATerm Epsilon (Bind AName ATerm)
  -- ET_appPlus and ET_appMinus:
  | AApp Epsilon ATerm ATerm
  | AAt ATerm Theta
  | ABoxLL ATerm Theta
  | ABoxLV ATerm
  | ABoxP ATerm Theta
  | AAbort ATerm
  | ATyEq ATerm ATerm
  | AJoin ATerm Int ATerm Int
  | AConv ATerm [(Epsilon,ATerm)] (Bind [AName] ATerm)
  -- First ATerm is proof, second is the type annotation.
  | AContra ATerm ATerm
  | ASmaller ATerm ATerm
  -- First ATerm is proof, other two are the ones we are comparing.
  | AOrdAx ATerm ATerm ATerm
  | AOrdTrans ATerm ATerm 
  -- ET_indPlus and ET_indMinus (the first ATerm is the (pi) type of the function):
  | AInd ATerm Epsilon (Bind (AName, AName) ATerm)
  -- ET_recPlus and ET_recMinus:
  | ARec ATerm Epsilon (Bind (AName, AName) ATerm)
  -- Why is let in the core language? To get more readable core terms.
  | ALet Theta Epsilon (Bind (AName, AName, Embed ATerm) ATerm)
   -- the final ATerm is the type of the entire match.
  | ACase ATerm (Bind AName [AMatch]) ATerm
  
{-
          -- | ATermination case
          | ATerminationCase ATerm (Bind AName (ATerm, (Bind AName ATerm)))    -- Proof
          -- | Derived form: assertion that t1 of type t2 terminates
-}
          
-- | A 'Match' represents a case alternative. The first 'AName' is the
-- constructor name, the rest of the 'AName's are pattern variables
deriving instance Show AMatch
data AMatch = AMatch AName (Bind [(AName, Epsilon)] ATerm)

data ADecl = ASig     Theta ATerm
           | AAxiom   Theta ATerm
           | ADef     Theta ATerm ATerm --Type, Term
           | AData    Telescope Theta Int [AConstructorDef]
           | AAbsData Telescope Theta Int
  deriving (Show)

data AConstructorDef = AConstructorDef AName ATelescope
  deriving (Show)

-------------
-- Annotated Telescopes
-------------
type ATelescope = [(AName,ATerm,Epsilon)]

-- | teleApp applies some term to all the variables in a telescope
aTeleApp :: ATerm -> ATelescope -> ATerm
aTeleApp tm tms =
  foldl (\a (nm,_,ep) -> AApp ep a (AVar nm)) tm tms

aTelePi :: ATelescope -> ATerm -> ATerm
aTelePi tele tyB =
  foldr (\(n,tm,ep) ret -> AArrow ep (bind (n,embed tm) ret))
        tyB tele

aDomTele :: ATelescope -> [AName]
aDomTele = map (\(v,_,_) -> v)

aDomTeleMinus :: ATelescope -> [AName]
aDomTeleMinus tele =
  [n | (n,_,ep) <- tele, ep == Erased]

aSwapTeleVars :: ATelescope -> [AName] -> ATelescope
aSwapTeleVars [] [] = []
aSwapTeleVars ((v,a,ep):tele) (v':vs) =
  (v',a,ep):(subst v (AVar v') $ aSwapTeleVars tele vs)
aSwapTeleVars _ _ =
  error "Internal error: lengths don't match in swapTeleVars"

aSetTeleEps :: Epsilon -> ATelescope -> ATelescope
aSetTeleEps ep = map (\(x,ty,_) -> (x,ty,ep))



------------------------
------------------------
--- Unannotated Language
------------------------
------------------------

deriving instance Show ETerm

-- ETerm for "erased" term
data ETerm = EVar EName
           -- Fixme: split into ETCon and EDCon (because they are different for isEValue)
           | ECon EName [ETerm]
           | EType Integer
           | EArrow Epsilon ETerm (Bind EName ETerm)
           | ELam (Bind EName ETerm)
           | EApp ETerm ETerm
           | ESmaller ETerm ETerm
           | EOrdAx
           | ETyEq ETerm ETerm
           | EJoin
           | EAbort
           | ERecPlus (Bind (EName, EName) ETerm)
           | ERecMinus (Bind EName ETerm)
           | ECase ETerm [EMatch]
           | ELet ETerm (Bind EName ETerm)
           | EContra
           | EAt ETerm Theta
           | ETerminationCase ETerm (Bind EName (ETerm, 
              (Bind EName ETerm)))
           | ETrustMe 

deriving instance Show EMatch
data EMatch = EMatch EName (Bind [EName] ETerm)

isEVar :: ETerm -> Maybe EName
isEVar (EVar n)   = Just n
isEVar _          = Nothing

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

$(derive [''Epsilon, ''Theta, ''Term, ''ETerm, ''ATerm, ''AMatch, ''EMatch])


instance Alpha Term

instance Alpha Theta
instance Alpha Epsilon

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Term Epsilon
instance Subst Term Theta

instance Alpha ATerm
instance Alpha AMatch

instance Subst ATerm ATerm where
  isvar (AVar x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst ATerm Epsilon
instance Subst ATerm Theta
instance Subst ATerm AMatch


instance Alpha ETerm
instance Alpha EMatch

instance Subst ETerm ETerm where
  isvar (EVar x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst ETerm EMatch
instance Subst ETerm Epsilon
instance Subst ETerm Theta


