{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, TypeFamilies, FlexibleInstances, FlexibleContexts,
              TemplateHaskell #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.CongruenceClosure(
 Constant(..), EqConstConst(..), EqBranchConst(..), Equation, WantedEquation(..),
 Proof(..),
  newState, propagate, reprs, unify, proofs, bindings
) where

{- This module mostly implements the algorithm from
     Robert Nieuwenhuis and Albert Oliveras, "Fast Congruence Closure and Extensions",
     Information and Computation, 205(4):557-580, April 2007.  
   Compared to that paper the main differences are:
    - The terms have n-ary branches instead of being just binary trees. This probably ruins the
      asymptotical running time of the algorithm, but it makes it more convenient to use.
    - the associated equality proofs are stored directly on the Union-Find edges, instead of
      in an associated "proof forest". (The algoritm will run faster, but the proof terms will
      be bigger than optimal).
 -}

import Prelude hiding (pi)

import Control.Monad
import Control.Applicative
import Data.Array.MArray
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy

newtype Constant = Constant Int
  deriving (Eq, Ord, Enum, Ix, Num)

instance Show Constant where
  show (Constant n) = show n

-- given equations a = b
data EqConstConst = EqConstConst Constant Constant
  deriving (Eq,Show)
-- given equations a1@a2 = b
data EqBranchConst label = EqBranchConst label [Constant] Constant
  deriving (Eq,Show)
-- wanted equations a = b
data WantedEquation = WantedEquation Constant Constant
  deriving (Eq,Ord,Show)

type Equation label = Either EqConstConst (EqBranchConst label)


-- Information we keep about a given equivalence class of constants
data ClassInfo proof = ClassInfo {
  classMembers  :: Set Constant,                  -- All elements in the class
  classVars     :: Set (CName proof,Constant),    -- All variables that are elements of the class; also remember which c they come from.
  classApps     :: Set (Label proof, [Constant]), -- All applications that are elements of the class
  essentialVars :: Set (CName proof)              -- variables that occur _inside_ _all_ members of the class
}

instance Show (ClassInfo proof) where
  show _ = "<classInfo>"


classSize :: (Proof proof) => ClassInfo proof -> Int
classSize cls = S.size (classMembers cls)

combineInfo :: (Proof proof) => ClassInfo proof -> ClassInfo proof -> ClassInfo proof
combineInfo a b =
  ClassInfo (S.union (classMembers a) (classMembers b))
            (S.union (classVars a) (classVars b))
            (S.union (classApps a) (classApps b))
            (S.intersection (essentialVars a) (essentialVars b))

-- Union-Find representatives.
type Reprs proof = Map Constant (Either (proof, Constant) (ClassInfo proof))
                                        -- (p:i=i', i')
type ExplainedEquation proof = (proof, Equation (Label proof))
type ExplainedEqBranchConst proof = (proof, EqBranchConst (Label proof))

class (Ord (Label proof), Ord (CName proof)) => Proof proof where
  type Label proof
  type CName proof   --names for unification variables

  refl :: Constant -> proof
  symm :: proof -> proof
  trans :: proof -> proof -> proof
  cong :: Label proof -> [proof] -> proof

data ProblemState proof = ProblemState {
  -- union-find structure mapping constants to their representative.
  reprs :: Reprs proof,

  -- maps c to list of equations l(a1..an)=b such that some ai is related to c.
  uses :: Map Constant [(proof, EqBranchConst (Label proof))],

  -- maps (l, (b1..bn)) to the input equation (l(a1..an)=a) with (bi..bn) representatives of (ai..an).
  --  If as |-> (ps, q,  bs=b) then:
  --   pi : bi = ai
  --   q  : bs = b.
  lookupeq :: Map ((Label proof),[Constant]) ([proof], proof, EqBranchConst (Label proof)),

  unboundVars :: Set (CName proof),           --Set of variables that can still be assigned.
  bindings    :: Map (CName proof) Constant,  --Assignment to unification variables
  proofs      :: Map WantedEquation proof
}

-- Most unification functions live inside a monad:
--  state to keep track of the problem state, plus list for making nondeterministic choices
type UniM proof a = StateT (ProblemState proof) [] a

-- Sets the union-find representative
setRepr :: Constant -> (Either (proof, Constant) (ClassInfo proof)) -> UniM proof ()
setRepr c val = modify (\st -> st{ reprs = M.insert c val (reprs st) })

giveBinding :: Proof proof => (CName proof) -> Constant -> UniM proof ()
giveBinding x val = modify (\st -> st{ bindings = M.insert x val (bindings st), 
                                       unboundVars = S.delete x (unboundVars st) })

giveProof :: WantedEquation -> proof -> UniM proof ()
giveProof e p = modify (\st -> st{ proofs  = M.insert e p (proofs st) })

-- Returns the representative of x.
find :: (Proof proof) => Constant -> UniM proof Constant
find x  = do
  (p, x') <- findExplain x
  return x'

-- Returns (p,x), where p proves (x = x')
findExplain :: (Proof proof) =>Constant -> UniM proof (proof,Constant)
findExplain x = do
  (p, x', size) <- findExplainInfo x
  return (p, x')

findExplains :: (Proof proof) =>  [Constant] -> UniM proof ([proof], [Constant])
findExplains ids = liftM unzip $ mapM findExplain ids

findExplainInfo :: (Proof proof) => Constant -> UniM proof (proof,Constant,ClassInfo proof)
findExplainInfo x = do
  content <- (M.!) <$> (gets reprs) <*> pure x
  case content of
    Left (p, x') -> do
       (q,x'',info) <- findExplainInfo x'
       if x'' /= x' 
         then do
           let r = (trans p q)
           setRepr x (Left (r, x'')) --path compression.
           return (r, x'', info)
         else 
           return (p,x',info)
    Right info  -> return (refl x, x, info)

-- Returns the old representative of the smaller class.
union :: Proof proof => Constant -> Constant -> proof -> UniM proof Constant
union x y p = do
  (q, x', xinfo) <- findExplainInfo x 
  (r, y', yinfo) <- findExplainInfo y
  if (classSize xinfo) < (classSize yinfo)
    then do
           setRepr x' (Left ((trans (symm q) (trans p r)), y'))
           setRepr y' (Right $ (xinfo `combineInfo` yinfo))
           return x'
    else do
           setRepr y' (Left ((trans (symm r) (trans (symm p) q)), x'))
           setRepr x' (Right $ (xinfo `combineInfo` yinfo))
           return y'

-- Add an application term to the equivalence class of a constant
recordApplication :: Proof proof => Constant -> (Label proof, [Constant]) -> UniM proof ()
recordApplication a app = do
  (_,a',ia) <- findExplainInfo a
  setRepr a' (Right $ ia{ classApps = S.insert app (classApps ia)})

-- propagate takes a list of given equations, and constructs the congruence
-- closure of those equations.
propagate :: Proof proof => [ExplainedEquation proof] -> UniM proof ()
propagate ((p, Left (EqConstConst a b)):eqs) = do
  alreadyEqual <- liftM2 (==) (find a) (find b)
  if not alreadyEqual
    then do
      a' <- union a b p
      a_uses <- M.findWithDefault [] a' <$> (gets uses)
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
       where r = trans (symm p) 
                       --(Branch l (map Leaf as))
                       (trans (cong l (zipWith3 (\pi ai' qi -> trans pi (symm qi)) ps as' qs))
                              --(Branch l (map Leaf bs))
                              q)
    Nothing -> do
      modify (\st ->
                 st{ lookupeq = M.insert (l,as') (ps, p, eq_a) (lookupeq st),
                     uses = M.unionWith (++) (M.fromList (map (\a' -> (a',[(p,eq_a)])) as')) (uses st)
                   }) 
      propagate eqs
propagate [] = return ()


-- If an equation is already in the congruence closure we can discard it.
unifyDelete :: Proof proof => WantedEquation -> UniM proof ()
unifyDelete  (WantedEquation a b) = do
  (p, a', ia) <- findExplainInfo a
  (q, b', ib) <- findExplainInfo b
  if a' == b'  --todo, replace with guard
   then do
           giveProof (WantedEquation a b) (trans p (symm q))
           return ()
   else
        lift []

-- If the lhs of a wanted equation is an evar, instantiate it with the rhs.
unifyBind :: Proof proof => WantedEquation -> UniM proof ()
unifyBind (WantedEquation a b) = do
  (_, _, ia) <- findExplainInfo a
  (_, _, ib) <- findExplainInfo b
  unbounds <- gets unboundVars
  let candidates = [ (x,c) | (x,c) <- (S.toList $ classVars ia), 
                             (x `S.member` unbounds), 
                             not (x `S.member` (essentialVars ib)) ]
  if not (null candidates) 
    then do
      let (x,c):_ = candidates    --If there are several variables, we don't care which one gets picked.
      giveBinding x b
      propagate [(refl c, Left $ EqConstConst c b)]
      --Now the equation ought to be trivial:
      unifyDelete (WantedEquation a b)
    else 
      lift []

-- If both sides of the equation are applications headed by the same label, try to unify the args.
unifyDecompose :: Proof proof => WantedEquation -> UniM proof ()
unifyDecompose (WantedEquation a b) = do
  (p, _, ia) <- findExplainInfo a
  (q, _, ib) <- findExplainInfo b
  (fa, as) <- lift $ S.toList $ classApps ia
  (fb, bs) <- lift $ S.toList $ classApps ib
  guard (fa == fb)
  unify $ zipWith WantedEquation as bs
  -- Now the equation should be trivial:
  unifyDelete (WantedEquation a b)
  return ()

-- Unify takes a list of wanted equations, and makes assignments to unification
-- variables to make all the equations true.
unify :: Proof proof => [WantedEquation] -> UniM proof ()
unify [] = return ()
unify (WantedEquation a b : wanted) = do
  unifyDelete (WantedEquation a b)
   `mplus`
   unifyBind (WantedEquation a b)
   `mplus` 
   (do unifyBind (WantedEquation b a) ; unifyDelete (WantedEquation a b))
   `mplus`
   unifyDecompose (WantedEquation a b)
  unify wanted

-- The list contains all the constants in the state, together with
--   * if the contant itself represents a variable, the name of the variable.
--   * the set of all variables that occurs in the term that the constant represents.
newState :: Proof proof => [(Constant,Maybe (CName proof), Set (CName proof))] -> ProblemState proof
newState constants  =
  ProblemState { reprs = M.fromList (map singletonClass constants) ,
                 uses = M.empty,
                 lookupeq = M.empty,
                 unboundVars = touchable,
                 bindings = M.empty,
                 proofs = M.empty}
 where singletonClass (c,mx,evars) = (c, Right $ ClassInfo (S.singleton c) 
                                                           (case mx of 
                                                              Nothing -> S.empty
                                                              Just x -> S.singleton (x, c))
                                                           S.empty 
                                                           evars)
       touchable = S.unions (map (\(_,_,evars) -> evars) constants)
