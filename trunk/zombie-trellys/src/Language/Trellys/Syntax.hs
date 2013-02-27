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

import Control.Monad.Writer
import Text.ParserCombinators.Parsec.Pos
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

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
            deriving (Read,Show,Eq,Bounded)

-- | Compute the least-upper bound on classifications.
lub :: Theta -> Theta -> Theta
lub Program _ = Program
lub _ Program = Program
lub x _ = x

instance Ord Theta where
  Logic <= Logic = True
  _ <= Program = True
  _ <= _ = False


------------------------------
------------------------------
--- Source Language
------------------------------
------------------------------

deriving instance Show Term

-- | The 'Term' representation is derived from the Ott language
-- definition. In the Trellys core, there is no distinction between
-- types and terms. Moreover, in contrast to the langauge definition,
-- we do not draw a distinction between names of datatypes and
-- constructors introduced via datatype definitions (and eliminated by
-- case expressions) and variables introduced by lambda abstractions
-- and dependent products).
data Term = Var TName    -- | variables
          | TCon TName [(Term,Epsilon)]   -- | type constructors (fully applied)
          | DCon TName [(Term,Epsilon)]   -- | term constructors (fully applied)
          | Type Int   -- | The 'Type' terminal
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
          -- | A complex case expression (only present in the surface language, not the core).
          --   The (Embed Term)s are scrutinees, the TNames are the scrutinee-pattern equations.
          | ComplexCase (Bind [(Embed Term, TName)] [ComplexMatch])
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
          -- | The 'unfold' expression, only present in the surface language.
          | Unfold Int Term       
          -- | @conv a by b at C@
          | Conv Term [(Term,Epsilon)] (Bind [TName] Term)
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
          | SubstitutedFor Term TName
          -- Marks where a term was substituted for a variable; used in elaborating
          --  the erased parts of conv-expressions.
          | SubstitutedForA ATerm TName
          -- Marks where an aterm was substituted for a variable; used in elaborating
          --  the proved parts of conv-expressions. 
          
-- | A 'Match' represents a case alternative. The first 'TName' is the
-- constructor name, the rest of the 'TName's are pattern variables
deriving instance Show Match
data Match = Match TName (Bind [(TName, Epsilon)] Term)  --the name is the constructor name.

-- | In the surface language, there is also ComplexMatch, which does several levels of 
-- pattern matching at once. These get elaborated into nested simple matches.

{- The list of [(TName,Embet ATerm)] is never used in the surface langauage. The idea is
   that
     ComplexMatch (bind [p1,p2] [(x1,embed a1), (x2,embed a2)] body)
   means
     p1, p2 => let x1 = a1 in
               let x2 = a2 in 
                 body
   This is used when elaborating complex case expressions into multiple simpler ones.
-}  

deriving instance Show ComplexMatch
data ComplexMatch = ComplexMatch (Bind [Pattern] Term)

deriving instance Show Pattern
data Pattern = PatCon (Embed TName) [(Pattern, Epsilon)]
             | PatVar TName

-- Todo: see if these are still needed.
delPosParenDeep :: Term -> Term
delPosParenDeep = everywhere (mkT delPosParen)
  where delPosParen :: Term -> Term
        delPosParen (Pos _ tm)             = tm
        delPosParen (Paren tm)             = tm
        delPosParen (SubstitutedFor  tm _) = tm
        delPosParen tm                     = tm

aDelPosParenDeep :: ATerm -> ATerm
aDelPosParenDeep = everywhere (mkT aDelPosParen)
  where aDelPosParen :: ATerm -> ATerm 
        aDelPosParen (ASubstitutedFor a _) = a
        aDelPosParen a                     = a

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

-- | replace all the (SubstitutedFor a x) with just x
unsubstitute :: ATerm -> ATerm 
unsubstitute = everywhere (mkT unsubstituteHere)
  where unsubstituteHere (ASubstitutedFor _ x) = (AVar x)
        unsubstituteHere e = e

-- | Gather all the terms occuring in ASubstitutedFor subterms.
extractSubstitution :: ATerm -> Map AName ATerm
extractSubstitution = everything M.union (mkQ M.empty mapping) 
  where mapping (ASubstitutedFor a x)   = M.singleton x a
        mapping _ = M.empty

data ConstructorNames = ConstructorNames {
                          tconNames :: Set TName,
                          dconNames :: Set TName
                        }
  deriving Show

emptyConstructorNames :: ConstructorNames 
emptyConstructorNames = ConstructorNames S.empty S.empty


-- | A Module has a name, a list of imports, a list of declarations,
--   and a list of constructor names (which affect parsing).     
data Module = Module { moduleName :: MName,
                       moduleImports :: [ModuleImport],
                       moduleEntries :: [Decl],
                       moduleConstructors :: ConstructorNames
                     }
            deriving (Show)

-- | A ModuleImport is just a name (for now).
newtype ModuleImport = ModuleImport MName
            deriving (Show,Eq)

data Decl = Sig  TName Theta Term
          | Axiom TName Theta Term
          | Def TName Term
          | Data TName Telescope Theta Int [ConstructorDef]
          | AbsData TName Telescope Theta Int
  deriving (Show)


-- | A Constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos TName Telescope
  deriving (Show)

-- | Goals (in the Coq sense), just used for pretty-printing so far.
data Goal = Goal [ADecl] --available context
                 ATerm   --type to be proven.

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
isVar (SubstitutedFor t x) = isVar t
isVar (Var n)   = Just n
isVar _         = Nothing

isAVar :: ATerm -> Bool
isAVar (AVar _) = True
isAVar _        = False

isType :: Term -> Maybe Int
isType (Pos _ t)  = isType t
isType (Paren t)  = isType t
isType (SubstitutedFor t x) = isType t
isType (Type n)   = Just n
isType _          = Nothing

isTyEq :: Term -> Maybe (Term, Term)
isTyEq (Pos _ t) = isTyEq t
isTyEq (Paren t) = isTyEq  t
isTyEq (SubstitutedFor t x) = isTyEq t
isTyEq (TyEq ty0 ty1) = Just (delPosParenDeep ty0, delPosParenDeep ty1)
isTyEq _ = Nothing

isSmaller :: Term -> Maybe (Term, Term)
isSmaller (Pos _ t) = isSmaller t
isSmaller (Paren t) = isSmaller t
isSmaller (SubstitutedFor t x) = isSmaller t
isSmaller (Smaller a b) = Just (delPosParenDeep a, delPosParenDeep b)
isSmaller _ = Nothing 

isArrow :: Term -> Maybe (Epsilon, Bind (TName, Embed Term) Term)
isArrow (Pos _ t)      = isArrow t
isArrow (Paren t)      = isArrow t
isArrow (SubstitutedFor t x) = isArrow t
isArrow (Arrow ep bnd) = Just (ep,bnd)
isArrow _              = Nothing

isAt :: Term -> Maybe (Term, Theta)
isAt (Pos _ t) = isAt t
isAt (Paren t) = isAt t
isAt (SubstitutedFor t x) = isAt t
isAt (At t th) = Just (t, th)
isAt _         = Nothing

isTCon :: Term -> Maybe (TName, [(Term,Epsilon)])
isTCon (Pos _ t) = isTCon t
isTCon (Paren t) = isTCon t
isTCon (SubstitutedFor t x) = isTCon t
isTCon (TCon c args) = Just (c, args)
isTCon _ = Nothing

isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (Paren t) = isNumeral t
isNumeral (SubstitutedFor t x) = isNumeral t
isNumeral (DCon c []) | c==string2Name "Zero" = Just 0
isNumeral (DCon c [(t,Runtime)]) | c==string2Name "Succ" =
  do n <- isNumeral t ; return (n+1)
isNumeral _ = Nothing

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
--   Given an environment, we can synthesize an unannotated (erased) term, a type, and a theta.

data ATerm = 
    AVar AName
  | AFO ATerm
  | ASquash ATerm
  | ACumul ATerm Int
  | AType Int
  | ATCon AName [ATerm] 
  | ADCon AName [ATerm] [(ATerm,Epsilon)]
  -- ET_arrow and ET_arrowImpred
  | AArrow   Epsilon (Bind (AName, Embed ATerm) ATerm)
  -- ET_lamPlus and ET_lamMinus. The first ATerm is the (pi) type of the entire lambda.
  | ALam ATerm  Epsilon (Bind AName ATerm)
  -- ET_appPlus and ET_appMinus. The last expression is the type of the entire application:
  | AApp Epsilon ATerm ATerm ATerm
  | AAt ATerm Theta
  | AUnboxVal ATerm
  | ABoxLL ATerm Theta
  | ABoxLV ATerm Theta
  | ABoxP ATerm Theta
  | AAbort ATerm
  | ATyEq ATerm ATerm
  | AJoin ATerm Int ATerm Int
  -- The last term is the type of the entire case-expression
  | AConv ATerm [(ATerm,Epsilon)] (Bind [AName] ATerm) ATerm
  -- First ATerm is proof, second is the type annotation.
  | AContra ATerm ATerm
  | ASmaller ATerm ATerm
  -- First ATerm is a proof of (a1 = c=1 b1 ... bn), the second one is the subterms bi.
  | AOrdAx ATerm ATerm 
  | AOrdTrans ATerm ATerm 
  -- ET_indPlus and ET_indMinus (the first ATerm is the (pi) type of the function):
  | AInd ATerm Epsilon (Bind (AName, AName) ATerm)
  -- ET_recPlus and ET_recMinus:
  | ARec ATerm Epsilon (Bind (AName, AName) ATerm)
  -- Why is let in the core language? To get more readable core terms.
  | ALet Epsilon (Bind (AName, AName, Embed ATerm) ATerm)
   -- the final ATerm is the type of the entire match.
  | ACase ATerm (Bind AName [AMatch]) ATerm
   -- the ATerm is the ascribed type
  | ATrustMe ATerm
  | ASubstitutedFor ATerm AName
  
{-
          -- | ATermination case
          | ATerminationCase ATerm (Bind AName (ATerm, (Bind AName ATerm)))    -- Proof
          -- | Derived form: assertion that t1 of type t2 terminates
-}
          
-- | A 'Match' represents a case alternative. The first 'AName' is the
-- constructor name, the rest of the 'AName's are pattern variables
deriving instance Show AMatch
data AMatch = AMatch AName (Bind [(AName, Epsilon)] ATerm)

data ADecl = ASig     AName Theta ATerm       --Type
           | ADef     AName ATerm             --Term
           | AData    AName ATelescope Theta Int [AConstructorDef]
           | AAbsData AName ATelescope Theta Int
  deriving (Show)

data AConstructorDef = AConstructorDef AName ATelescope
  deriving (Show)

data AHint = AHint AName Theta ATerm --The type

data AModule = AModule { aModuleName :: MName,
                         aModuleEntries :: [ADecl]
                       }

declname :: ADecl -> AName
declname (ASig x _ _) = x
declname (ADef x _) = x
declname (AData x _ _ _ _) = x
declname (AAbsData x _ _ _) = x

-------------
-- Annotated Telescopes
-------------
type ATelescope = [(AName,ATerm,Epsilon)]

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
           | ETCon EName [ETerm]
           | EDCon EName [ETerm]
           | EType Int
           | EArrow Epsilon ETerm (Bind EName ETerm)
           | ELam (Bind EName ETerm)
           | EILam ETerm             --erased lambda
           | EApp ETerm ETerm
           | EIApp ETerm             --erased application
           | ESmaller ETerm ETerm
           | EOrdAx
           | ETyEq ETerm ETerm
           | EJoin
           | EAbort
           | ERecPlus (Bind (EName, EName) ETerm)
           | ERecMinus (Bind EName ETerm)
           | EIndPlus (Bind (EName, EName) ETerm)
           | EIndMinus (Bind EName ETerm)
           | ECase ETerm [EMatch]
           | ELet ETerm (Bind EName ETerm)
           | EContra
           | EAt ETerm Theta
--           | ETerminationCase ETerm (Bind EName (ETerm, 
--              (Bind EName ETerm)))
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

$(derive [''Epsilon, ''Theta, ''Term, ''Match, ''ComplexMatch, 
         ''ETerm, ''Pattern, ''EMatch, 
         ''ATerm, ''AMatch, ''ADecl, ''AConstructorDef])


instance Alpha Term
instance Alpha Match
instance Alpha ComplexMatch
instance Alpha Pattern
instance Alpha Theta
instance Alpha Epsilon
instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

-- aterms should never contain term variables.
instance Subst Term ATerm where
  isvar _ = Nothing
instance Subst Term AMatch where

instance Subst Term Epsilon
instance Subst Term Theta
instance Subst Term Match
instance Subst Term ComplexMatch
instance Subst Term Pattern

instance Alpha ATerm
instance Alpha AMatch
instance Alpha ADecl
instance Alpha AConstructorDef

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
