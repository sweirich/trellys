{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, TypeFamilies, FlexibleInstances, FlexibleContexts #-}

module Language.Trellys.CongruenceClosure(
 Constant(..), EqConstConst(..), EqBranchConst(..), Equation, 
 Proof(..),
  newState, find, propagate, reprs,
  printState
) where

{- This module mostly implements the algorithm from
     Robert Nieuwenhuis and Albert Oliveras, "Fast Congruence Closure and Extensions",
     Information and Computation, 205(4):557-580, April 2007.  
   Compared to that paper the main differences are:
    - The terms have n-ary branches instead of being just binary trees. This probably ruins the
      asymptotical running time of the algorithm, but it makes it more convenient to use.
    - the associated equality proofs are stored directly on the Union-Find edges, instead of
      in an associated "proof forest".
 -}

import Control.Monad
import Control.Monad.ST
import Control.Arrow (first,second)
import Data.Array.MArray
import Data.Array.ST
import Data.Either
import Data.Maybe (isJust, fromJust)
import Data.Tuple (swap)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as List
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM

import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import Control.Monad.Writer.Lazy
import Data.Functor.Identity

import System.IO.Unsafe

import Test.QuickCheck
import Test.QuickCheck.Monadic (PropertyM, assert, monadicST, forAllM, pick, pre, run)
import Test.QuickCheck.Gen as Gen
import qualified Test.HUnit as HU

newtype Constant = Constant Int
  deriving (Eq, Ord, Enum, Ix, Num)

instance Show Constant where
  show (Constant n) = show n

-- equations a = b
data EqConstConst = EqConstConst Constant Constant
  deriving (Eq,Show)
-- equations a1@a2 = b
data EqBranchConst label = EqBranchConst label [Constant] Constant
  deriving (Eq,Show)

type Equation label = Either EqConstConst (EqBranchConst label)

-- A convenient monad for recording an association between terms and constants.
newtype NamingT t m a = NamingT (StateT (Bimap t Constant, [Constant]) m a)
  deriving (Monad, MonadTrans)

recordName :: (Monad m, Ord t) => t -> NamingT t m Constant
recordName t = NamingT $ do
                 (mapping, (c:cs)) <- get
                 case BM.lookup t mapping of
                   Nothing -> do put (BM.insert t c mapping, cs)
                                 return c
                   Just c' -> return c'

runNamingT :: (Monad m) => NamingT t m a -> [Constant] -> m (a, Bimap t Constant)
runNamingT (NamingT m) constantSupply = liftM (second fst) $ runStateT m (BM.empty, constantSupply)

type Naming t = NamingT t Identity
runNaming :: Naming  t  a -> [Constant] -> (a, Bimap t Constant)
runNaming m nameSupply  = runIdentity $ runNamingT m nameSupply

-- Union-Find representatives.
-- The Int represents the number of elements in the equivalence class.
type Reprs proof s = STArray s Constant (Either (proof, Constant) Int)
                                              -- (p:i=i', i')
type ExplainedEquation proof = (proof, Equation (Label proof))
type ExplainedEqBranchConst proof = (proof, EqBranchConst (Label proof))

class (Ord (Label proof)) => Proof proof where
  type Label proof

  refl :: Constant -> proof
  symm :: proof -> proof
  trans :: proof -> proof -> proof
  cong :: Label proof -> [proof] -> proof

data ProblemState proof s = ProblemState {
  -- union-find structure mapping constants to their representative.
  reprs :: Reprs proof s,
  -- maps c to list of equations a1@a2=b such that ai related to c.
  uses :: Map Constant [(proof, EqBranchConst (Label proof))],
  -- maps (l, (b1..bn)) to the input equation (l(a1..an)=a) with (bi..bn) representatives of (ai..an).
  --  If as |-> (ps, q,  bs=b) then:
  --   pi : bi = ai
  --   q  : bs = b.
  lookupeq :: Map ((Label proof),[Constant]) ([proof], proof, EqBranchConst (Label proof))
}

-- Returns the representative of id.
find :: (Proof proof) => Constant -> Reprs proof s -> ST s Constant
find id reprs = do
  (p, id') <- findExplain id reprs
  return id'

-- Returns (p,id'), where p proves (Leaf id = Leaf id')
findExplain :: (Proof proof) =>Constant -> Reprs proof s -> ST s (proof,Constant)
findExplain id reprs = do
  (p, id', size) <- findExplainSize id reprs
  return (p, id')

findExplains :: (Proof proof) =>  [Constant] -> Reprs proof s -> ST s ([proof], [Constant])
findExplains ids reprs = liftM unzip $ mapM (`findExplain` reprs) ids

findExplainSize :: (Proof proof) => Constant -> Reprs proof s -> ST s (proof,Constant,Int)
findExplainSize id reprs = do
  content <- readArray reprs id
  case content of
    Left (p, id') -> do
       (q,id'',size) <- findExplainSize id' reprs
       if id'' /= id' 
         then do
           let r = (trans p q)
           writeArray reprs id (Left (r, id'')) --path compression.
           return (r, id'', size)
         else 
           return (p,id',size)
    Right size  -> return (refl id, id, size)

-- Returns the old representative of the smaller class.
union :: Proof proof => Constant -> Constant -> proof -> Reprs proof s -> ST s Constant
union x y p reprs = do
  (q, x', xsize) <- findExplainSize x reprs
  (r, y', ysize) <- findExplainSize y reprs
  if xsize < ysize
    then do
           writeArray reprs x' (Left ((trans (symm q) (trans p r)), y'))
           writeArray reprs y' (Right $ xsize+ysize)
           return x'
    else do
           writeArray reprs y' (Left ((trans (symm r) (trans (symm p) q)), x'))
           writeArray reprs x' (Right $ xsize+ysize)
           return y'

propagate :: Proof proof => ProblemState proof s -> [ExplainedEquation proof] -> ST s (ProblemState proof s)
propagate st ((p, Left (EqConstConst a b)):eqs) = do
  alreadyEqual <- liftM2 (==) (find a (reprs st)) (find b (reprs st))
  if not alreadyEqual
    then do
      a' <- union a b p (reprs st)
      propagate st (map (\(p,eq) -> (p, (Right eq))) (M.findWithDefault [] a' (uses st)) ++ eqs)
   else 
      propagate st eqs
propagate st ((p, Right eq_a@(EqBranchConst l as a)):eqs) = do
  (ps, as') <- findExplains as (reprs st)
  case M.lookup (l, as') (lookupeq st) of
    Just (qs, q, eq_b@(EqBranchConst _ bs b)) -> 
      propagate st ((r, Left (EqConstConst a b)):eqs)
       where r = trans (symm p) 
                       --(Branch l (map Leaf as))
                       (trans (cong l (zipWith3 (\pi ai' qi -> trans pi (symm qi)) ps as' qs))
                              --(Branch l (map Leaf bs))
                              q)
    Nothing -> do
      propagate st{ lookupeq = M.insert (l,as') (ps, p, eq_a) (lookupeq st),
                    uses = M.unionWith (++) (M.fromList (map (\a' -> (a',[(p,eq_a)])) as')) (uses st)
                } 
                eqs
propagate st [] = return st

newState :: (Constant,Constant) -> ST s (ProblemState proof s)
newState (i0,i1) = do
  reprs <- newArray (i0,i1) (Right 1)
  return $ ProblemState { reprs = reprs,
                          uses = M.empty,
                          lookupeq = M.empty }

{- ################## Testing ################################# -}

-- Simple example of a term language and proofs.
data TermLabel = TermLabel String
  deriving (Eq, Ord)
instance Show TermLabel where
  show (TermLabel s) = s

data Term = Leaf Constant
          | Branch TermLabel [Term]
  deriving (Show, Eq, Ord)

data Explanation =
    Assumption (Equation TermLabel)
  | Refl Term
  | Symm Explanation
  | Trans Explanation Term Explanation
  | Cong TermLabel [Explanation]
 deriving (Eq,Show)

instance Proof Explanation where
  type Label Explanation = TermLabel
  refl = Refl . Leaf
  symm = Symm
  trans pf1 pf2 = Trans pf1 c pf2
                    where (_,c) = explanationToTerms pf1
         
  cong = Cong

-- Simplifying proofs: push in Symm, note that Refl is a unit for Trans.
simplExplanation :: Explanation -> Explanation
simplExplanation e@(Assumption _) = e
simplExplanation e@(Refl _) = e
simplExplanation (Symm p) = (symmExplanation p)
 where symmExplanation (Assumption h) = Symm (Assumption h)
       symmExplanation (Refl t) = (Refl t)
       symmExplanation (Symm p) = simplExplanation p
       symmExplanation (Trans p1 t p2) = simplExplanation (Trans (symmExplanation p2) 
                                                                 t 
                                                                 (symmExplanation p1))
       symmExplanation (Cong l ps) = Cong l (map symmExplanation ps)
simplExplanation (Trans p1 t p2) =
  case simplExplanation p1 of
    (Refl _) -> simplExplanation p2
    p1' -> case simplExplanation p2 of
             (Refl _) -> p1'
             p2' -> (Trans p1' t p2')
simplExplanation (Cong l ps) = Cong l (map simplExplanation ps)

explanationToTerms :: Explanation -> (Term,Term)
explanationToTerms (Assumption (Left (EqConstConst a b))) = (Leaf a, Leaf b)
explanationToTerms (Assumption (Right (EqBranchConst l as b))) = (Branch l (map Leaf as), Leaf b)
explanationToTerms (Refl a) = (a,a)
explanationToTerms (Symm p) = swap (explanationToTerms p)
explanationToTerms (Trans p c q) = (a,b)
                                   where (a,_) = explanationToTerms p
                                         (_,b) = explanationToTerms q
explanationToTerms (Cong l ps) = (Branch l (map fst abs), Branch l (map snd abs))
                                   where abs = map explanationToTerms ps

checkExplanation :: Term -> Term -> Explanation -> Bool
checkExplanation (Leaf a) (Leaf b) (Assumption (Left (EqConstConst a' b'))) 
  | a==a' && b==b'
  = True
checkExplanation (Branch l as) (Leaf b) (Assumption (Right (EqBranchConst l' as' b'))) 
  | l==l' && as==(map Leaf as') && b==b'
  = True
checkExplanation a a' (Refl a'') 
  | a==a' && a' == a''
  = True
checkExplanation a b (Symm p)
  | checkExplanation b a p
  = True
checkExplanation a c (Trans p b q)
  | checkExplanation a b p && checkExplanation b c q
  = True
checkExplanation (Branch l as) (Branch l' bs) (Cong l'' ps)
  | l==l' && l'==l'' 
    && length as==length bs && length bs==length ps 
    && and (zipWith3 checkExplanation as bs ps)
  = True
checkExplanation a b p 
  = unsafePerformIO (putStr ("Bogus proof:\n" ++ show a ++ "\n" ++ show b ++ "\n" ++ show p ++ "\n"))
    `seq` False

-- QuickCheck infrastructure
instance Arbitrary Constant where
  arbitrary = oneof $ map (return.Constant) [0..4]
instance Arbitrary TermLabel where
  arbitrary = oneof $ map (return . TermLabel) ["a", "b"]
instance Arbitrary Term where
  arbitrary = sized term 
    where term 0 = liftM Leaf arbitrary
          term n = do k <- choose (1,4)
                      oneof [ liftM Leaf arbitrary,
                              liftM2 Branch arbitrary (vectorOf k (term (n `div` k))) ]
instance Arbitrary EqConstConst where
  arbitrary = liftM2 EqConstConst arbitrary arbitrary
instance Arbitrary (EqBranchConst TermLabel) where
  arbitrary = do 
    k <- choose (1,4)
    liftM3 EqBranchConst arbitrary (vectorOf k arbitrary) arbitrary

forAll2M :: (Monad m, Show a) => Gen a -> (a -> a -> PropertyM m b) -> PropertyM m b
forAll2M gen p = do
  a1 <- pick gen
  a2 <- pick gen
  p a1 a2

congTest :: [Equation TermLabel] -> Term -> Term -> Bool
congTest eqs a b = isJust (congTestExplain eqs a b)

congTestExplain :: [Equation TermLabel] -> Term -> Term -> Maybe Explanation
congTestExplain eqs a b =
  let (((acnst, bcnst), eqsAB), naming) = runNaming (runWriterT $ liftM2 (,) (genEqs a) (genEqs b)) [Constant 6..]
      cmax = maximum ((Constant 5) : BM.keysR naming)
  in runST $ do
       st <- newState (Constant 0, cmax)
       st <- propagate st (   map (\eq -> (Assumption eq, eq)) eqs 
                           ++ map (\eq -> (Refl (fst (equationToTerms (Right eq))), Right eq)) eqsAB)
       (p1, acnst') <- findExplain acnst (reprs st)
       (p2, bcnst') <- findExplain bcnst (reprs st)
       if acnst' == bcnst'
         then return $ Just (substDefnsExplanation naming $ Trans p1 (Leaf acnst') (Symm p2))
         else return Nothing

-- Take a term to think about and name each subterm in it with a separate constant,
-- while at the same time recording equations relating terms to their subterms.
genEqs :: Term -> WriterT [EqBranchConst TermLabel] (Naming Term) Constant
genEqs (Leaf x) = return x
genEqs (Branch l ts) = do
  a  <- lift $ recordName (Branch l ts)
  bs <- mapM genEqs ts
  tell [EqBranchConst l bs a]
  return a

-- substitute the terms in the bimap for the constants.
substDefns :: Bimap Term Constant -> Term -> Term
substDefns naming (Branch l as) = Branch l (map (substDefns naming) as)
substDefns naming (Leaf c) = case BM.lookupR c naming of
                               Nothing -> Leaf c
                               Just t -> substDefns naming t

substDefnsExplanation :: Bimap Term Constant -> Explanation -> Explanation
substDefnsExplanation naming pf@(Assumption _) = pf
substDefnsExplanation naming (Refl a) = Refl (substDefns naming a)
substDefnsExplanation naming (Symm pf) = Symm (substDefnsExplanation naming pf)
substDefnsExplanation naming (Trans pf1 t pf2) = Trans (substDefnsExplanation naming pf1)
                                                       (substDefns naming t)
                                                       (substDefnsExplanation naming pf2)
substDefnsExplanation naming (Cong l pfs) = Cong l (map (substDefnsExplanation naming) pfs)

equationToTerms :: Equation TermLabel -> (Term,Term)
equationToTerms (Left (EqConstConst a b)) = (Leaf a, Leaf b)
equationToTerms (Right (EqBranchConst l as b)) = (Branch l (map Leaf as), Leaf b)

merges :: ProblemState Explanation s -> [Equation TermLabel] -> ST s (ProblemState Explanation s)
merges st eqs = propagate st [(Assumption eq, eq) | eq <- eqs]

-- Printing algorithm-state for debugging purposes:
printReprs :: (Show proof) => Reprs proof s -> ST s String
printReprs reprs = do
  (i0,i1) <- getBounds reprs
  ss <- mapM (\i -> do 
                      cnt <- readArray reprs i
                      return $ "\n" ++ show i ++ " => " ++ show cnt ++ " ")
             [i0 .. i1]
  return $ concat ss

printLookupeq :: (Show proof, Show (Label proof)) =>
                 Map (Label proof,[Constant]) ([proof], proof, EqBranchConst (Label proof)) -> String
printLookupeq l = "fromList [" ++ concat (List.intersperse "," $ map (\((l,as), (_,_,eq)) -> show (l,as) ++ ", (_,_," ++ show eq ++ ")") (M.toList l)) ++ "]"

printState :: (Show proof, Show (Label proof)) => ProblemState proof s -> ST s  String
printState (ProblemState reprs uses lookupeq) = do
  repr_s <- printReprs reprs
  return $ "\nreprs = " ++ repr_s 
           ++ ", \nuses = " ++ show uses
           ++ ", \nlookupeq = " ++ printLookupeq lookupeq
                                           
{- Tests -}

test2 = runST $ do
  st <- newState (Constant 0, Constant 6)
  st <- merges st [Right (EqBranchConst (TermLabel "a")  [Constant 1,Constant 2] (Constant 5)),Right (EqBranchConst (TermLabel "a") [Constant 3,Constant 4] (Constant 6)), Left (EqConstConst (Constant 1) (Constant 3))]
  printState st

test3 = runST $ do
  st <- newState (Constant 0, Constant 6)
  st <- merges st [Left (EqConstConst 4 1),Left (EqConstConst 2 3),Right (EqBranchConst (TermLabel "a") [2,3,1,2] 4),Right (EqBranchConst (TermLabel "a") [2,2,3,1] 1),Right (EqBranchConst (TermLabel "b") [2,2,2,3] 0),Left (EqConstConst 4 2),Right (EqBranchConst (TermLabel "a") [4,4] 0)]
  printState st


testbug = runST $ do
  st <- newState (Constant 0, Constant 18)
  st <- merges st  [
    Right $ EqBranchConst (TermLabel "Succ") [Constant 2]               (Constant 1),
    Left $ EqConstConst (Constant 0) (Constant 1),
    Right $ EqBranchConst (TermLabel "Succ") [Constant 2]               (Constant 1),
    Right $ EqBranchConst (TermLabel "@")    [Constant 8, Constant 1]   (Constant 7),
    Right $ EqBranchConst (TermLabel "@")    [Constant 7, Constant 9]   (Constant 6),
    Right $ EqBranchConst (TermLabel "@")    [Constant 5, Constant 6]   (Constant 4),
    Right $ EqBranchConst (TermLabel "Succ") [Constant 2]               (Constant 1),
    Right $ EqBranchConst (TermLabel "@")    [Constant 4, Constant 1]   (Constant 3),
    Right $ EqBranchConst (TermLabel "@")    [Constant 8, Constant 2]   (Constant 13),
    Right $ EqBranchConst (TermLabel "@")    [Constant 13, Constant 9]   (Constant 12),
    Right $ EqBranchConst (TermLabel "@")    [Constant 5, Constant 12]   (Constant 11),
    Right $ EqBranchConst (TermLabel "@")    [Constant 11, Constant 0]   (Constant 10),
    Left $ EqConstConst (Constant 3) (Constant 10),
    Right $ EqBranchConst (TermLabel "@")    [Constant 8, Constant 2]   (Constant 13),
    Right $ EqBranchConst (TermLabel "@")    [Constant 13, Constant 9]   (Constant 12),
    Right $ EqBranchConst (TermLabel "@")    [Constant 5, Constant 12]   (Constant 11),
    Right $ EqBranchConst (TermLabel "@")    [Constant 11, Constant 0]   (Constant 10),
    Right $ EqBranchConst (TermLabel "@")    [Constant 8, Constant 0]   (Constant 17),
    Right $ EqBranchConst (TermLabel "@")    [Constant 17, Constant 9]   (Constant 16),
    Right $ EqBranchConst (TermLabel "@")    [Constant 5, Constant 16]   (Constant 15),
    Right $ EqBranchConst (TermLabel "@")    [Constant 15, Constant 0]   (Constant 14)]
  (p1, acnst') <- findExplain (Constant 10) (reprs st)
  (p2, bcnst') <- findExplain (Constant 14) (reprs st)
  if acnst' == bcnst'
    then return $ Just (simplExplanation (Trans p1 (Leaf acnst') (Symm p2)))
    else return Nothing

{-- The High-level specification of the algorithm -}

-- the relation congTest contains the input equations:
prop_containsEqs :: (NonEmptyList (Equation TermLabel)) -> Property
prop_containsEqs  (NonEmpty eqs) = 
  forAll (Gen.elements eqs) (uncurry (congTest eqs) . equationToTerms)

-- the relation congTest is a congruence (FIXME: should test for n-ary branches):
prop_congruence :: [Equation TermLabel] -> TermLabel -> Term -> Term -> Term -> Term -> Property
prop_congruence eqs l a a' b b' =
  congTest eqs a a' ==> congTest eqs b b' ==> congTest eqs (Branch l [a, b]) (Branch l [a', b'])

-- it's the least congruence, or equivantly, it contains only provable equations.
-- (Fixme: the statement of this property needs work.)
prop_soundness :: [Equation TermLabel] -> Term -> Term -> Property
prop_soundness eqs a b = 
  isJust p ==> checkExplanation a b (simplExplanation (fromJust p))
  where p = congTestExplain eqs a b
  
{- Some lower-level invariants maintained by the algorithm -}

-- All critical pairs in the rewrite system lookupeq are trivial.
prop_criticalPairs :: [Equation TermLabel] -> Property
prop_criticalPairs eqs = monadicST $ do
    st <- run $ newState (Constant 0, Constant 6)
    st <- run $ merges st eqs
    pre (not (M.null (lookupeq st)))
    forAll2M (Gen.elements (M.toList $ lookupeq st))
      (\((l1,as), (_, _, EqBranchConst _ _ a)) ((l2,bs), (_, _, EqBranchConst _ _ b)) -> do
         as' <- run $ mapM (`find` (reprs st)) as
         a'  <- run $ find a (reprs st)
         bs' <- run $ mapM (`find` (reprs st)) bs
         b'  <- run $ find b (reprs st)
         pre (l1==l2 && as'==bs')
         assert (a'==b'))

-- lookupeq does not forget any of the BranchConst input equations.
prop_lookupeqNonlossy :: [Equation TermLabel] -> Property
prop_lookupeqNonlossy eqs  = monadicST $ do
    st <- run $ newState (Constant 0, Constant 6)
    st <- run $ merges st eqs
    let (_,bcEqs) = partitionEithers eqs
    pre (not (null bcEqs))
    forAllM (Gen.elements bcEqs)
      (\(EqBranchConst l as a) -> do
        (_,as') <- run $ findExplains as (reprs st)
        (_,a')  <- run $ findExplain a (reprs st)
        case M.lookup (l,as') (lookupeq st) of
          Nothing -> assert False
          Just (_, _, EqBranchConst l' bs b) -> do
            b' <- run $ find b (reprs st)
            assert (l==l' && a'== b'))  

-- All proofs recorded on the Union-find arcs are valid.
prop_validProofsArcs :: [Equation TermLabel] -> Property
prop_validProofsArcs eqs = monadicST $ do
    st <- run $ newState (Constant 0, Constant 6)
    st <- run $ merges st eqs
    assocs <- run $ getAssocs (reprs st)
    forAllM (Gen.elements assocs)
      (\(a, e) -> 
         case e of
           Left (p,b) -> assert $ checkExplanation (Leaf a) (Leaf b) p
           Right info -> assert True)

-- All proofs recorded with the lookupeqs are valid.
prop_validProofsLookups :: [Equation TermLabel] -> Property
prop_validProofsLookups eqs = monadicST $ do
    st <- run $ newState (Constant 0, Constant 6)
    st <- run $ merges st eqs
    pre (not (M.null (lookupeq st)))
    forAllM (Gen.elements (M.toList $ lookupeq st))
      (\((l,as),(ps, q, EqBranchConst _ bs b)) -> 
         assert $ and (zipWith3 checkExplanation (map Leaf bs) (map Leaf as) ps)
                  && checkExplanation (Branch l (map Leaf bs)) (Leaf b) q)

assertQC :: Testable prop => String -> prop -> HU.Assertion
assertQC msg p = do
   res <- quickCheckResult p
   case res of
     Success { } -> return ()
     _ -> HU.assertFailure (msg ++ " " ++ show res)

testsuite = HU.runTestTT $ HU.TestList [
             HU.TestCase $ assertQC "the relation should contain the input equations" prop_containsEqs,
             HU.TestCase $ assertQC "the relation should be a congruence"  prop_congruence,
             HU.TestCase $ assertQC "the relation should be sound" prop_soundness,
             HU.TestCase $ assertQC "lookupEq should cover the input equations" prop_lookupeqNonlossy,
             HU.TestCase $ assertQC "lookupEq should not have critical pairs" prop_criticalPairs,
             HU.TestCase $ assertQC "all union-find proofs should be valid" prop_validProofsArcs,
             HU.TestCase $ assertQC "all proofs stored in lookupeqs should be valid" prop_validProofsLookups
            ]
