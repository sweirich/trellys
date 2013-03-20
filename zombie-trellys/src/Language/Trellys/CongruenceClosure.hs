{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.CongruenceClosure(
 Constant(..), EqConstConst(..), EqBranchConst(..), Equation, 
 Proof(..),
  newState, propagate, reprs, isEqual
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

import Language.Trellys.GenericBind (Name)


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

type Equation label = Either EqConstConst (EqBranchConst label)


type CName = Name Constant

-- Information we keep about a given equivalence class of constants
data ClassInfo proof = ClassInfo {
  classMembers  :: Set Constant,                  -- All elements in the class
  classApps     :: Set (Label proof, [Constant]), -- All applications that are elements of the class
  essentialVars :: Set CName       -- variables that occur _inside_ _all_ members of the class
}

instance Show (ClassInfo proof) where
  show _ = "<classInfo>"


classSize :: (Proof proof) => ClassInfo proof -> Int
classSize cls = S.size (classMembers cls)

combineInfo :: (Proof proof) => ClassInfo proof -> ClassInfo proof -> ClassInfo proof
combineInfo a b =
  ClassInfo (S.union (classMembers a) (classMembers b))
            (S.union (classApps a) (classApps b))
            (S.intersection (essentialVars a) (essentialVars b))

-- Union-Find representatives.
type Reprs proof = Map Constant (Either (proof, Constant) (ClassInfo proof))
                                        -- (p:i=i', i')
type ExplainedEquation proof = (proof, Equation (Label proof))
type ExplainedEqBranchConst proof = (proof, EqBranchConst (Label proof))

class (Ord (Label proof)) => Proof proof where
  type Label proof

  refl :: Constant -> proof
  symm :: proof -> proof
  trans :: proof -> proof -> proof
  cong :: Label proof -> [proof] -> proof

data ProblemState proof = ProblemState {
  -- union-find structure mapping constants to their representative.
  reprs :: Reprs proof,
  -- maps c to list of equations a1@a2=b such that ai related to c.
  uses :: Map Constant [(proof, EqBranchConst (Label proof))],
  -- maps (l, (b1..bn)) to the input equation (l(a1..an)=a) with (bi..bn) representatives of (ai..an).
  --  If as |-> (ps, q,  bs=b) then:
  --   pi : bi = ai
  --   q  : bs = b.
  lookupeq :: Map ((Label proof),[Constant]) ([proof], proof, EqBranchConst (Label proof)),

  unboundVars :: Set Constant  --Set of variables that can still be assigned.
}

-- Most unification functions live inside a monad:
--  state to keep track of the problem state, plus list for making nondeterministic choices
type UniM proof a = StateT (ProblemState proof) [] a

-- Sets the union-find representative
setRepr :: Constant -> (Either (proof, Constant) (ClassInfo proof)) -> UniM proof ()
setRepr c val = modify (\st -> st{ reprs = M.insert c val (reprs st) })

-- Add an equation to the uses table.
--addUse :: Constant -> (proof, EqBranchConst (Label proof)) -> UniM proof ()
--addUse c = undefined

-- Add an equation to the lookupeq table.

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

-- If a and b are in the same equivalence class return a proof of that, otherwise return Nothing. 
isEqual :: (Proof proof) => Constant -> Constant  -> UniM proof proof
isEqual a b = do
  (p, a') <- findExplain a 
  (q, b') <- findExplain b
  if a' == b' 
   then return $ (trans p (symm q))
   else lift []

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

-- Unify takes a list of wanted equations, and makes assignments to unification
-- variables to make all the equations true.
unify :: Proof proof => [WantedEquation] -> UniM proof ()
unify = undefined

newState :: (Constant,Constant) -> ProblemState proof
newState (i0,i1) =
  ProblemState { reprs = M.fromList [ (c, Right $ singletonClass c) | c <- [i0 .. i1] ] ,
                 uses = M.empty,
                 lookupeq = M.empty,
                 unboundVars = S.empty }
 where singletonClass c = ClassInfo (S.singleton c)  S.empty S.empty
