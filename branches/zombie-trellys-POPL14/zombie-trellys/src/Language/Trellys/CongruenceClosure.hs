{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, TypeFamilies, FlexibleInstances, FlexibleContexts,
              TemplateHaskell ,
    RankNTypes #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.CongruenceClosure(
 Constant(..), EqConstConst(..), EqBranchConst(..), Equation, WantedEquation(..),
 Proof(..),
  ProblemState, proofs, bindings, naming,
  newState, recordName, propagate, 
  classMembersExplain,
  unify, -- main function, runState is run for UniM monad  
) where

{- This module mostly follows two papers. The congruence closure part is based on
     Robert Nieuwenhuis and Albert Oliveras, "Fast Congruence Closure and Extensions",
     Information and Computation, 205(4):557-580, April 2007.  
   Compared to that paper the main differences are:
    - The terms have n-ary branches instead of being just binary trees. This probably ruins the
      asymptotical running time of the algorithm, but it makes it more convenient to use.
    - the associated equality proofs are stored directly on the Union-Find edges, instead of
      in an associated "proof forest". (The algoritm will run faster, but the proof terms will
      be bigger than optimal).

   The rigid E-unification part is based on
     Jean Goubalt, "A Rule-based Algorithm for Rigid E-Unification".
   However, compared to that paper, only a subset of the rules are currently implemented, namely
   the deterministic ones (i.e. the ones that do not involve nondeterministic search): Norm, Delete,
   Decomp, and Bind.
 -}

import Prelude hiding (pi)
import Control.Monad 
import Control.Applicative
import Data.Array.MArray
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict

import Language.Trellys.Syntax (ATerm, AName, Label, Proof(..), isAUniVar, uniVars)

newtype Constant = Constant Int
  deriving (Eq, Ord, Enum, Ix, Num)

instance Show Constant where
  show (Constant n) = show n

-- given equations a = b
data EqConstConst = EqConstConst Constant Constant
  deriving (Eq,Show)
-- given equations a1@a2 = b
data EqBranchConst  = EqBranchConst Label [Constant] Constant
  deriving (Eq,Show)
-- wanted equations a = b
data WantedEquation = WantedEquation Constant Constant
  deriving (Eq,Ord,Show)

type Equation = Either EqConstConst EqBranchConst


-- Information we keep about a given equivalence class of constants
data ClassInfo  = ClassInfo {
  classMembers  :: Set Constant,                  -- All elements in the class
  classVars     :: Set (AName,Constant),    -- All variables that are elements of the class; 
                                                  ---  also remember which c they correspond to.
  classApps     :: Set (Label, [Constant]), -- All applications that are elements of the class
  essentialVars :: Set AName                -- variables that occur _inside_ _all_ members of the class
}

instance Show ClassInfo where
  show _ = "<classInfo>"


classSize :: ClassInfo -> Int
classSize cls = S.size (classMembers cls)

combineInfo :: ClassInfo -> ClassInfo  -> ClassInfo 
combineInfo a b =
  ClassInfo (S.union (classMembers a) (classMembers b))
            (S.union (classVars a) (classVars b))
            (S.union (classApps a) (classApps b))
            (S.intersection (essentialVars a) (essentialVars b))

-- Union-Find representatives.
type Reprs = Map Constant (Either (Proof, Constant) ClassInfo)
                                        -- (p:i=i', i')
type ExplainedEquation = (Proof, Equation)
type ExplainedEqBranchConst = (Proof, EqBranchConst)

data ProblemState = ProblemState {
  -- union-find structure mapping constants to their representative.
  reprs :: Reprs,

  -- maps c to list of equations l(a1..an)=b such that some ai is related to c.
  uses :: Map Constant [(Proof, EqBranchConst)],

  -- maps (l, (b1..bn)) to the input equation (l(a1..an)=a) with (bi..bn) representatives of (ai..an).
  --  If as |-> (ps, q,  bs=b) then:
  --   pi : bi = ai
  --   q  : bs = b.
  lookupeq :: Map (Label,[Constant]) ([Proof], Proof, EqBranchConst),

--  types       :: Map Constant Constant,       --Maps constants representing expressions to constants
--                                              -- representing the type of the expression.

  unboundVars :: Set AName,           --Set of variables that can still be assigned.
  bindings    :: Map AName Constant,  --Assignment to unification variables
  proofs      :: Map WantedEquation Proof,

  -- Recall the mapping between constants and the ATerms they denote.
  naming      :: Bimap ATerm Constant
}


-- | Allocate a new name (Constant) for a subterm.
recordName :: (Applicative m, Monad m) => ATerm -> StateT ProblemState m Constant
recordName a = do
  existing <- BM.lookup a <$> gets naming
  case existing of 
    Just c -> 
      return c
    Nothing -> do
      st <- get
      let c = if M.null (reprs st)
                then 0
                else fst (M.findMax (reprs st)) + 1
      let singletonClass = ClassInfo{ classMembers = S.singleton c,
                                      classVars = case isAUniVar a of
                                                    Nothing -> S.empty
                                                    Just x -> S.singleton (x, c),
                                      classApps = S.empty,
                                      essentialVars = uniVars a }
      put (st{ reprs = M.insert c (Right singletonClass) (reprs st),
               unboundVars = (unboundVars st) `S.union` (uniVars a),
               naming = BM.insert a c (naming st) })
      return c

-- The list contains all the constants in the state, together with
--   * if the contant itself represents a variable, the name of the variable.
--   * the set of all variables that occurs in the term that the constant represents.
newState :: ProblemState
newState =
  ProblemState{reprs = M.empty,
               uses = M.empty,
               lookupeq = M.empty,
               unboundVars = S.empty,
               bindings = M.empty,
               proofs = M.empty,
               naming = BM.empty}

-- Most unification functions live inside a monad:
--  state to keep track of the problem state, plus list for making nondeterministic choices.
--
-- The Union-Find structure does not do any backtracking, so those functions are more polymorphic
-- andn live in (Monad m) => (StateT (ProblemState proof) m).
type UniM a = StateT ProblemState [] a

-- Sets the union-find representative
setRepr :: (Monad m) => Constant -> (Either (Proof, Constant) ClassInfo) -> StateT ProblemState m ()
setRepr c val = modify (\st -> st{ reprs = M.insert c val (reprs st) })

giveBinding :: AName -> Constant -> UniM ()
giveBinding x val = modify (\st -> st{ bindings = M.insert x val (bindings st), 
                                       unboundVars = S.delete x (unboundVars st) })

giveProof :: WantedEquation -> Proof -> UniM ()
giveProof e p = modify (\st -> st{ proofs  = M.insert e p (proofs st) })

-- Returns the representative of x.
find :: Monad m => Constant -> StateT ProblemState m Constant
find x  = do
  (p, x') <- findExplain x
  return x'

-- Returns (p,x), where p proves (x = x')
findExplain :: Monad m =>Constant -> StateT ProblemState m (Proof,Constant)
findExplain x = do
  (p, x', size) <- findExplainInfo x
  return (p, x')

findExplains :: Monad m =>  [Constant] -> StateT ProblemState m ([Proof], [Constant])
findExplains ids = liftM unzip $ mapM findExplain ids

findExplainInfo :: Monad m => Constant -> StateT ProblemState m (Proof,Constant,ClassInfo)
findExplainInfo x = do
  content <- return (M.!) `ap` (gets reprs) `ap` return x
  case content of
    Left (p, x') -> do
       (q,x'',info) <- findExplainInfo x'
       if x'' /= x' 
         then do
           let r = (RawTrans p q)
           setRepr x (Left (r, x'')) --path compression.
           return (r, x'', info)
         else 
           return (p,x',info)
    Right info  -> return (RawRefl, x, info)

-- Given a constant, return all the constants in its equivalence class,
--  and a proof that they are equal.
classMembersExplain :: Monad m => Constant -> StateT ProblemState m [(Constant, Proof)]
classMembersExplain x = do
  (p, x', xinfo) <- findExplainInfo x
  mapM (\y -> do
          (q, y') <- findExplain y
          return $ (y, RawTrans p (RawSymm q)))
       (S.toList $ classMembers xinfo)

-- Returns the old representative of the smaller class.
union :: Monad m => Constant -> Constant -> Proof -> StateT ProblemState m Constant
union x y p = do
  (q, x', xinfo) <- findExplainInfo x 
  (r, y', yinfo) <- findExplainInfo y
  if (classSize xinfo) < (classSize yinfo)
    then do
           setRepr x' (Left ((RawTrans (RawSymm q) (RawTrans p r)), y'))
           setRepr y' (Right $ (xinfo `combineInfo` yinfo))
           return x'
    else do
           setRepr y' (Left ((RawTrans (RawSymm r) (RawTrans (RawSymm p) q)), x'))
           setRepr x' (Right $ (xinfo `combineInfo` yinfo))
           return y'

-- Add an application term to the equivalence class of a constant
recordApplication :: Monad m => Constant -> (Label, [Constant]) 
                     -> StateT ProblemState m ()
recordApplication a app = do
  (_,a',ia) <- findExplainInfo a
  setRepr a' (Right $ ia{ classApps = S.insert app (classApps ia)})

-- propagate takes a list of given equations, and constructs the congruence
-- closure of those equations.
propagate :: Monad m => [ExplainedEquation] -> StateT ProblemState m ()
propagate ((p, Left (EqConstConst a b)):eqs) = do
  alreadyEqual <- liftM2 (==) (find a) (find b)
  if not alreadyEqual
    then do
      a' <- union a b p
      a_uses <- M.findWithDefault [] a' `liftM` (gets uses)
      propagate (map (\(q,eq) -> (q, (Right eq))) a_uses ++ eqs)
   else 
      propagate eqs
propagate ((p, Right eq_a@(EqBranchConst l as a)):eqs) = do
  recordApplication a (l,as)
  (ps, as') <- findExplains as
  lookupeqs <- gets lookupeq
  case M.lookup (l, as') lookupeqs of
    Just (qs, q, eq_b@(EqBranchConst _ bs b)) -> 
      propagate ((r, Left (EqConstConst a b)):eqs)
       where r = RawTrans (RawSymm p) 
                       --(Branch l (map Leaf as))
                       (RawTrans (RawCong l (zipWith3 (\pi ai' qi -> RawTrans pi (RawSymm qi)) ps as' qs))
                              --(Branch l (map Leaf bs))
                              q)
    Nothing -> do
      modify (\st ->
                 st{ lookupeq = M.insert (l,as') (ps, p, eq_a) (lookupeq st),
                     uses = M.unionWith (++) (M.fromList (map (\a' -> (a',[(p,eq_a)])) as')) (uses st)
                   }) 
      propagate eqs
propagate [] = return ()


-- Take a computation that can succeed in multiple ways, and only
--  consider the first way that works.
cut :: UniM a -> UniM a
cut m = StateT $ 
          \s -> take 1 (runStateT m s)

-- Nondeterministically choose between two computations. If the first
-- one suceeds, then commit to that choice and don't try the second.
mplusCut :: UniM a -> UniM a -> UniM a
mplusCut m1 m2 = StateT $
                 \s -> let r1 = runStateT m1 s
                           r2 = runStateT m2 s
                        in
                          if not (null r1) then r1 else r2

type Tracer = forall a. String -> WantedEquation -> a -> a

-- If an equation is already in the congruence closure we can discard it.
unifyDelete :: Tracer -> WantedEquation -> UniM ()
unifyDelete tracer  (WantedEquation a b) = do
  (p, a', ia) <- findExplainInfo a
  (q, b', ib) <- findExplainInfo b
  guard (a' == b')
  giveProof (WantedEquation a b) (RawTrans p (RawSymm q))
  tracer "Deleted" (WantedEquation a b) (return ())

-- If the lhs of a wanted equation is an evar, instantiate it with the rhs.
unifyBind :: Tracer -> WantedEquation -> UniM  ()
unifyBind tracer (WantedEquation a b) = do
  (_, _, ia) <- findExplainInfo a
  (_, _, ib) <- findExplainInfo b
  unbounds <- gets unboundVars
  let candidates = [ (x,c) | (x,c) <- (S.toList $ classVars ia), 
                             (x `S.member` unbounds), 
                             not (x `S.member` (essentialVars ib)) ]
  guard $ not (null candidates) 
  let (x,c):_ = candidates    --If there are several variables, we don't care which one gets picked.
  giveBinding x b
  propagate [(RawRefl, Left $ EqConstConst c b)]
  --Now the equation ought to be trivial:
  unifyDelete tracer (WantedEquation a b)
  tracer "Bound" (WantedEquation a b) (return ())

-- If both sides of the equation are applications headed by the same label, try to unify the args.
unifyDecompose :: Tracer -> Set WantedEquation -> WantedEquation -> UniM ()
unifyDecompose tracer visited (WantedEquation a b) = do
  (p, _, ia) <- findExplainInfo a
  (q, _, ib) <- findExplainInfo b
  (fa, as) <- lift $ S.toList $ classApps ia
  (fb, bs) <- lift $ S.toList $ classApps ib
  guard (fa == fb)
  tracer "About to Decompose" (WantedEquation a b) $ do
    unify tracer (S.insert (WantedEquation a b) visited) (zipWith WantedEquation as bs)
    -- Now the equation should be trivial:
    unifyDelete tracer (WantedEquation a b)
    return ()
  tracer "Decomposed" (WantedEquation a b) (return ())

-- Unify takes a list of wanted equations, and makes assignments to unification
-- variables to make all the equations true.
-- It also tracks a set of "visited" equations (think depth-first-search) in order to
-- not get stuck in a loop.
unify :: Tracer -> Set WantedEquation -> [WantedEquation] -> UniM ()
unify tracer visited [] = return ()
unify tracer visited (WantedEquation a b : wanted) = do
           guard (not (S.member (WantedEquation a b) visited))
           unifyDelete tracer (WantedEquation a b)
            `mplusCut`
            unifyBind tracer (WantedEquation a b)
            `mplusCut` 
            (do unifyBind tracer (WantedEquation b a) ; unifyDelete tracer (WantedEquation a b))
            `mplusCut`
            unifyDecompose tracer visited (WantedEquation a b)
           unify tracer visited wanted

