{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    UndecidableInstances, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | This module captures the base abstract syntax of Trellys core. It
-- uses the generic locally nameless representation of binders from the
-- LangLib package.
module Language.Trellys.Syntax where

import Generics.RepLib hiding (Arrow,Con)
import qualified Generics.RepLib as RL

import Language.Trellys.GenericBind

import Control.Monad.Writer
import Control.Monad.State
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

orEps :: Epsilon -> Epsilon -> Epsilon
orEps Erased _ = Erased
orEps _ Erased = Erased
orEps Runtime Runtime = Runtime

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

deriving instance Ord Epsilon

data EvaluationStrategy = CBV | PAR_CBV
  deriving (Show)

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
          -- | Concrete syntax is !e
          | Explicitize Term          
          -- | A let expression (bound name, equality name, value)
          | Let Theta Epsilon (Bind (TName, TName, Embed Term) Term)
          -- | Dependent functions: (x : A )_{ep} -> B
          | Arrow  Explicitness Epsilon (Bind (TName, Embed Term) Term)
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
          -- | The 'join' expression, written @join k1 k2@ or @pjoin k1 k2@  We
          -- bidirectionally infer the terms
          | Join Int Int EvaluationStrategy
          -- | The 'unfold' expression, only present in the surface language.
          | Unfold Int Term Term
          -- | @contra a@ says @a@ is a contradiction and has any type
          | Contra Term
          -- If a proves (c a1 .. an)=(c b1 .. bn),  then (injectivity a i) proves ai=bi
          | InjDCon Term Int
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
        delPosParen tm                     = tm

-- | Partial inverse of Pos
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _         = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: Term -> Maybe SourcePos
unPosDeep = something (mkQ Nothing unPos)

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
          | Data TName Telescope Int [ConstructorDef]
          | AbsData TName Telescope Int
          | UsuallyTheta (Maybe Theta)
  deriving (Show)


-- | A Constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos TName Telescope
  deriving (Show)

-- | Goals (in the Coq sense), just used for pretty-printing so far.
data Goal = Goal [(Theta,ATerm,ATerm)] --available context
                 ATerm   --type to be proven.

-------------
-- Telescopes
-------------

-- Unlike the ATelescope definition, this datatype does not pay attention to 
-- proper binding structure. It's convenient to be able to use ordinary list functions.
type Telescope = [(TName,Term,Epsilon)]

--------------
-- Basic query and manipulation functions on source terms
--------------
isVar :: Term -> Maybe TName
isVar (Pos _ t) = isVar t
isVar (Paren t) = isVar t
isVar (Var n)   = Just n
isVar _         = Nothing

isAVar :: ATerm -> Bool
isAVar (AVar _) = True
isAVar _        = False

isAType :: ATerm -> Bool
isAType (AType _) = True
isAType _ = False

isTyEq :: Term -> Maybe (Term, Term)
isTyEq (Pos _ t) = isTyEq t
isTyEq (Paren t) = isTyEq  t
isTyEq (TyEq ty0 ty1) = Just (delPosParenDeep ty0, delPosParenDeep ty1)
isTyEq _ = Nothing

isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (Paren t) = isNumeral t
isNumeral (DCon c []) | c==string2Name "Zero" = Just 0
isNumeral (DCon c [(t,Runtime)]) | c==string2Name "Succ" =
  do n <- isNumeral t ; return (n+1)
isNumeral _ = Nothing

---------------------------------------
---------------------------------------
-- Annotated Core Language
---------------------------------------
---------------------------------------

type AName = Name ATerm

deriving instance Show ATerm

-- Infered vs Explicit arguments. 
-- Defining a special-case Alpha instance means that aeq/acompare will not
-- look at these annotations, but one can still distinguish them by pattern-matching.
data Explicitness = Explicit | Inferred
  deriving Show

instance Alpha Explicitness where
   aeq' c _ _  = True
   acompare' c _ _  = EQ

-- | ATerm are annotated terms.
--   Given an environment, we can synthesize an unannotated (erased) term, a type, and a theta.

data ATerm = 
    AVar AName
  | AUniVar AName ATerm --the second ATerm is the type of the univar. Todo: Probably we should keep the context also.
  | ACumul ATerm Int 
  | AType Int
  | ATCon AName [ATerm] 
    
      -- Theta is the max th of any argument
  | ADCon AName Theta [ATerm] [(ATerm,Epsilon)]

  -- ET_arrow and ET_arrowImpred
  -- Int is the Type-level of this Type
  | AArrow Int Explicitness Epsilon (Bind (AName, Embed ATerm) ATerm)

  -- ET_lamPlus and ET_lamMinus. The first ATerm is the (pi) type of the entire lambda.
  | ALam Theta ATerm  Epsilon (Bind AName ATerm)
  -- ET_appPlus and ET_appMinus. The last expression is the type of the entire application:
  | AApp Epsilon ATerm ATerm ATerm
  | AAt ATerm Theta
  | AUnbox ATerm
  | ABox ATerm Theta
  | AAbort ATerm
  | ATyEq ATerm ATerm
  | AJoin ATerm Int ATerm Int EvaluationStrategy
  -- first ATerm is the subject of the conversion, the second ATerm is the equality proof.
  | AConv ATerm ATerm
  -- The last term is the RHS of the equation we are proving
  --  (The erased parts of it may differ from what you get if you substitute the RHSs of
  --   the individual equations into the template).
  | ACong [ATerm] (Bind [AName] ATerm) ATerm
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
  | ALet Epsilon (Bind (AName, AName, Embed ATerm) ATerm) (Theta,ATerm)
   -- the final ATerm is the type of the entire match.
  | ACase ATerm (Bind AName [AMatch]) (Theta,ATerm)
   -- Decomposing equalities
  | AInjDCon ATerm Int
  | ADomEq ATerm
  | ARanEq ATerm ATerm ATerm
  | AAtEq ATerm
  | ANthEq Int ATerm
   -- the ATerm is the ascribed type
  | ATrustMe ATerm
  
{-
          -- | ATermination case
          | ATerminationCase ATerm (Bind AName (ATerm, (Bind AName ATerm)))    -- Proof
          -- | Derived form: assertion that t1 of type t2 terminates
-}
          
-- | A 'Match' represents a case alternative. The first 'AName' is the
-- constructor name, the telescope are the pattern variables (together with their types).
deriving instance Show AMatch
data AMatch = AMatch AName (Bind ATelescope ATerm)

data ADecl = ASig     AName Theta ATerm       --Type
           | ADef     AName ATerm             --Term
           | AData    AName ATelescope Int [AConstructorDef]
           | AAbsData AName ATelescope Int
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
declname (AData x _ _ _) = x
declname (AAbsData x _ _) = x

getLastDef :: [ADecl] -> Maybe (AName,ATerm)
getLastDef decs = gld decs Nothing
  where
    gld :: [ADecl] -> Maybe (AName,ATerm) -> Maybe (AName,ATerm)
    gld [] acc         = acc
    gld (dec:decs) acc = 
      case dec of
        ADef an at -> gld decs (Just (an,at))
        _          -> gld decs acc

-------------
-- Annotated Telescopes
-------------
data ATelescope = AEmpty
                | ACons (Rebind (AName, Embed ATerm,Epsilon) ATelescope)
  deriving Show
 
aTeleLength :: ATelescope -> Int
aTeleLength AEmpty = 0
aTeleLength (ACons (unrebind->(_,tele))) = 1 + (aTeleLength tele)

aAppendTele :: ATelescope -> ATelescope -> ATelescope
aAppendTele AEmpty tele = tele
aAppendTele (ACons (unrebind->(t,tele1))) tele2 =
 ACons (rebind t (aAppendTele tele1 tele2))

aTeleErasedVars :: ATelescope -> Set AName
aTeleErasedVars AEmpty = S.empty
aTeleErasedVars (ACons (unrebind->((x,_,ep),tele))) =
  (if ep==Erased then S.singleton x else S.empty) 
   `S.union` aTeleErasedVars tele

aTeleEpsilons :: ATelescope -> [Epsilon]
aTeleEpsilons AEmpty = []
aTeleEpsilons (ACons (unrebind->((_,_,ep),tele))) =
  ep : aTeleEpsilons tele

aSetTeleEps :: Epsilon -> ATelescope -> ATelescope
aSetTeleEps ep AEmpty = AEmpty
aSetTeleEps ep (ACons (unrebind -> ((x,ty,_),tele))) =
  ACons (rebind (x,ty,ep) (aSetTeleEps ep tele))

aTeleAsArgs :: ATelescope -> [(ATerm,Epsilon)]
aTeleAsArgs AEmpty = []
aTeleAsArgs (ACons (unrebind->((x,ty,ep),tele))) =
  (AVar x,ep) : (aTeleAsArgs tele)

--------------------------------------
-- Simplifying substitution
--------------------------------------

{- Suppose that somewhere inside a typing derivation we have
   (AUnbox x) for some variable x, and then want to substitute
   (ABox a) for x, where a is some non-value expression.  If we just
   constructed the derivation (AUnbox (ABox a)) it would violate
   the value restriction of Unbox.

   This case is actually very common for the regularity premise of the
   function application rule. In the case when a function
   argument has an @-type, we implicitly use Unbox to check that the
   function type is well-kinded, and also implicitly use Box at the
   call site to give the argument the right type. So it's
   important to do something about this.

   Here, I define a function to simplify away such Unbox-Box pairs.

   Probably one should try harder than this, but more sophisticated 
   simplifications would require type information.
 -}


simplUnboxBox :: Rep a => a -> a
simplUnboxBox = RL.everywhere (RL.mkT simplUnboxBoxOnce)
  where simplUnboxBoxOnce :: ATerm -> ATerm 
        simplUnboxBoxOnce (AUnbox (ABox a _)) = a
        simplUnboxBoxOnce a = a

simplSubst :: Subst b a => Name b -> b -> a -> a
simplSubst x b a = simplUnboxBox $ subst x b a

simplSubsts :: Subst b a => [(Name b, b)] -> a -> a
simplSubsts xs a =  simplUnboxBox $ substs xs a

---------------------------------------
-- Some random utility functions
---------------------------------------

-- Picks fresh names for each of the variables in the telecope.
-- The names will be fresh versions of the given strings.
freshATele :: (Functor m, Fresh m) => [String] -> ATelescope -> m ATelescope
freshATele [] AEmpty = return AEmpty
freshATele (s:ss) (ACons (unrebind->((x,ty,ep),t))) = do
   x' <- fresh (string2Name s)
   t' <- freshATele ss (subst x (AVar x') t)
   return $ ACons (rebind (x',ty,ep) t')
freshATele [] _ = error "wrong number of strings given to freshATele--too many args"
freshATele _  AEmpty = error "wrong number of strings given to freshATele--too many strings"

-- | (substATele bs delta a) substitutes the b's for the variables in delta in a.
-- Precondition: bs and delta have the same lenght.
substATele :: Subst ATerm a => ATelescope -> [ATerm] -> a -> a
substATele AEmpty [] a = a
substATele (ACons (unrebind->((x,ty,ep),tele))) (b:bs) a = substATele tele bs (simplSubst x b a)
substATele _ _ _ = error "internal error: substATele called with unequal-length arguments"

------------------------
------------------------
--- Unannotated Language
------------------------
------------------------

deriving instance Show ETerm

-- ETerm for "erased" term
data ETerm = EVar EName
           | EUniVar EName 
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

$(derive [''Epsilon, ''Theta, ''Explicitness, ''EvaluationStrategy, 
         ''Term, ''Match, ''ComplexMatch, 
         ''ETerm, ''Pattern, ''EMatch, 
         ''ATerm, ''AMatch, ''ADecl, ''AConstructorDef, ''ATelescope ])


instance Alpha Term
instance Alpha Match
instance Alpha ComplexMatch
instance Alpha Pattern
instance Alpha Theta
instance Alpha Epsilon
instance Alpha EvaluationStrategy

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

-- aterms should never contain term variables.
instance Subst Term ATerm where
  isvar _ = Nothing
instance Subst Term AMatch
instance Subst Term ATelescope

instance Subst Term Epsilon
instance Subst Term Explicitness
instance Subst Term Theta
instance Subst Term EvaluationStrategy

instance Subst Term Match
instance Subst Term ComplexMatch
instance Subst Term Pattern

instance Alpha ATerm
instance Alpha AMatch
instance Alpha ADecl
instance Alpha AConstructorDef
instance Alpha ATelescope

instance Subst ATerm ATerm where
  isvar (AVar x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst ATerm Epsilon
instance Subst ATerm Explicitness
instance Subst ATerm Theta
instance Subst ATerm EvaluationStrategy

instance Subst ATerm AMatch
instance Subst ATerm ATelescope

instance Alpha ETerm
instance Alpha EMatch

instance Subst ETerm ETerm where
  isvar (EVar x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst ETerm EMatch
instance Subst ETerm Epsilon
instance Subst ETerm Explicitness
instance Subst ETerm Theta

instance Eq ETerm where
  (==) = aeq
instance Ord ETerm where
  compare = acompare

instance Eq ATerm where
  (==) = aeq
instance Ord ATerm where
  compare = acompare

-----------------------------------------------------------
-- Equational reasoning proofs, constructed by the 
-- congruence closure implementation.
------------------------------------------------------------

{- I try to keep this somewhat minimal. If Haskell had a 
   ML-like module system I would expose this as a formalized 
   interface, and CongruenceClosure.hs would be a functor depending on it.
 -}

-- The unification code needs to be aware of which things are 
-- unification variables.
isAUniVar :: ATerm -> Maybe AName
isAUniVar (AUniVar x _) = Just x
isAUniVar _ = Nothing

-- | Gather all unification variables that occur in a term.
uniVars :: ATerm -> Set AName 
uniVars = RL.everything S.union (RL.mkQ S.empty uniVarsHere) 
  where uniVarsHere (AUniVar x _)   = S.singleton x
        uniVarsHere  _ = S.empty

-- Also, need to know which head forms have injectivity rules.
-- Note: sadly we can't make this work for Pi-types.
isInjectiveLabel :: Label -> Bool
isInjectiveLabel l = isInjective a
  where (_,a) = unsafeUnbind l
        isInjective :: ATerm -> Bool
        isInjective (AAt _ _) = True
        isInjective (ATCon _ _) = True
        --isInjective (ADCon _ _ _ _) = True --Dcon is more tricky, because of value restriction.
        isInjective _ = False

isEqualityLabel :: Label -> Bool 
isEqualityLabel l = isATyEq a
  where (_,a) = unsafeUnbind l
        isATyEq (ATyEq _ _) = True
        isATyEq _ = False

-- Labels for non-atomic terms.
type Label = Bind [AName] ATerm

instance Eq Label where
  (==) = aeq
instance Ord Label where
  compare = acompare

-- The datatype of proofs. 
data Proof =
   -- RawAssumption (x, C, p, A, B) 
   --- means that x:C and p:C=(A=B).
   --The first component is either a proof term which the type elaborator constructed
   -- (usually just a variable, sometimes unbox applied to a variable),
   -- or a (join 0 0) which genEqs (in EqualityReasoning.hs) put in.
   RawAssumption (ATerm, ATerm, Proof, ATerm, ATerm) 
 | RawRefl
 | RawSymm Proof
 | RawTrans Proof Proof
 | RawCong Label [Proof]
 | RawInj Int Proof 
 deriving (Show,Eq)


$(derive [''Proof])
