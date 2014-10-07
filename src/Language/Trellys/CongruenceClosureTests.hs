{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, TypeFamilies, 
             FlexibleInstances, FlexibleContexts, ViewPatterns,
             TemplateHaskell, RankNTypes #-}

{- This does not compile, some time I should think about how to do unit tests
   for the congruence closure algorithm again -}

import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.List
import Data.Maybe
import Data.Tuple
import Data.Either
import Data.Map (Map)
import qualified Data.Map as M
import Data.Functor.Identity
import Control.Applicative
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer

import Language.Trellys.GenericBind
import Language.Trellys.Syntax hiding (Term)
import Language.Trellys.CongruenceClosure hiding (recordName)

import System.IO.Unsafe
import Test.QuickCheck hiding (label)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic, forAllM, pick, pre, run)
import Test.QuickCheck.Gen as Gen
import qualified Test.HUnit as HU


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


data Term = 
   Leaf Constant
 | Branch Label [Term]

-- Simplifying proofs: push in RawSymm, note that RawRefl is a unit for RawTrans.
simplProof :: Proof -> Proof
simplProof e@(RawAssumption _) = e
simplProof e@RawRefl = e
simplProof (RawSymm p) = (symmProof p)
 where symmProof (RawAssumption h) = RawSymm (RawAssumption h)
       symmProof (RawRefl t) = (RawRefl t)
       symmProof (RawSymm p) = simplProof p
       symmProof (RawTrans p1 t p2) = simplProof (RawTrans (symmProof p2) 
                                                                 t 
                                                                 (symmProof p1))
       symmProof (RawCong l ps) = RawCong l (map symmProof ps)
simplProof (RawTrans p1 t p2) =
  case simplProof p1 of
    (RawRefl _) -> simplProof p2
    p1' -> case simplProof p2 of
             (RawRefl _) -> p1'
             p2' -> (RawTrans p1' t p2')
simplProof (RawCong l ps) = RawCong l (map simplProof ps)

explanationToTerms :: Proof -> (Term,Term)
explanationToTerms (RawAssumption (Left (EqConstConst a b))) = (Leaf a, Leaf b)
explanationToTerms (RawAssumption (Right (EqBranchConst l as b))) = (Branch l (map Leaf as), Leaf b)
explanationToTerms (RawRefl a) = (a,a)
explanationToTerms (RawSymm p) = swap (explanationToTerms p)
explanationToTerms (RawTrans p c q) = (a,b)
                                   where (a,_) = explanationToTerms p
                                         (_,b) = explanationToTerms q
explanationToTerms (RawCong l ps) = (Branch l (map fst abs), Branch l (map snd abs))
                                   where abs = map explanationToTerms ps

checkProof :: Term -> Term -> Proof -> Bool
checkProof (Leaf a) (Leaf b) (RawAssumption (Left (EqConstConst a' b'))) 
  | a==a' && b==b'
  = True
checkProof (Branch l as) (Leaf b) (RawAssumption (Right (EqBranchConst l' as' b'))) 
  | l==l' && as==(map Leaf as') && b==b'
  = True
checkProof a a' (RawRefl a'') 
  | a==a' && a' == a''
  = True
checkProof a b (RawSymm p)
  | checkProof b a p
  = True
checkProof a c (RawTrans p b q)
  | checkProof a b p && checkProof b c q
  = True
checkProof (Branch l as) (Branch l' bs) (RawCong l'' ps)
  | l==l' && l'==l'' 
    && length as==length bs && length bs==length ps 
    && and (zipWith3 checkProof as bs ps)
  = True
checkProof a b p 
  = unsafePerformIO (putStr ("Bogus proof:\n" ++ show a ++ "\n" ++ show b ++ "\n" ++ show p ++ "\n"))
    `seq` False

label :: String -> Label
label = bind [] . AVar. string2Name
-- QuickCheck infrastructure
instance Arbitrary Label where
  arbitrary = oneof $ map label  ["a", "b"]
instance Arbitrary Term where
  arbitrary = sized term 
    where term 0 = liftM Leaf (oneof [0..4])
          term n = do k <- choose (1,4)
                      oneof [ liftM Leaf [oneof 0..4] ,
                              liftM2 Branch arbitrary (vectorOf k (term (n `div` k))) ]
instance Arbitrary EqConstConst where
  arbitrary = liftM2 EqConstConst arbitrary arbitrary
instance Arbitrary EqBranchConst  where
  arbitrary = do 
    k <- choose (1,4)
    liftM3 EqBranchConst arbitrary (vectorOf k arbitrary) arbitrary

forAll2M :: (Monad m, Show a) => Gen a -> (a -> a -> PropertyM m b) -> PropertyM m b
forAll2M gen p = do
  a1 <- pick gen
  a2 <- pick gen
  p a1 a2

congTest :: [Equation] -> Term -> Term -> Bool
congTest eqs a b = isJust (congTestExplain eqs a b)

congTestExplain :: [Equation] -> Term -> Term -> Maybe Proof
congTestExplain eqs a b =
  let (((acnst, bcnst), eqsAB), naming) = runNaming (runWriterT $ liftM2 (,) (genEqs a) (genEqs b)) [6..]
      cmax = maximum ((5) : BM.keysR naming)
  in flip evalState (newState ( 0, cmax)) $ do
       propagate (   map (\eq -> (RawAssumption eq, eq)) eqs 
                  ++ map (\eq -> (RawRefl (fst (equationToTerms (Right eq))), Right eq)) eqsAB)
       fmap (substDefnsProof naming) <$> equalTestExplain acnst bcnst

equalTestExplain :: Constant -> Constant -> State ProblemState (Maybe Proof)
equalTestExplain a b = do
  (p, a') <- findExplain a
  (q, b') <- findExplain b
  if (a' == b')
    then return (Just (RawTrans p (RawSymm q)))
    else return Nothing

-- Take a term to think about and name each subterm in it with a separate constant,
-- while at the same time recording equations relating terms to their subterms.
genEqs :: Term -> WriterT [EqBranchConst] (Naming Term) Constant
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

substDefnsProof :: Bimap Term Constant -> Proof -> Proof
substDefnsProof naming pf@(RawAssumption _) = pf
substDefnsProof naming (RawRefl a) = RawRefl (substDefns naming a)
substDefnsProof naming (RawSymm pf) = RawSymm (substDefnsProof naming pf)
substDefnsProof naming (RawTrans pf1 t pf2) = RawTrans (substDefnsProof naming pf1)
                                                       (substDefns naming t)
                                                       (substDefnsProof naming pf2)
substDefnsProof naming (RawCong l pfs) = RawCong l (map (substDefnsProof naming) pfs)

equationToTerms :: Equation -> (Term,Term)
equationToTerms (Left (EqConstConst a b)) = (Leaf a, Leaf b)
equationToTerms (Right (EqBranchConst l as b)) = (Branch l (map Leaf as), Leaf b)

merges :: ProblemState -> [Equation] -> (ProblemState)
merges st eqs = execState (propagate [(RawAssumption eq, eq) | eq <- eqs]) st


-- Printing algorithm-state for debugging purposes: 
{-
printReprs :: (Show proof) => IntMap (Either (Proof, Constant) ClassInfo) -> String
printReprs reprs = do
  concatMap (\(i, cnt) -> "\n" ++ show i ++ " => " ++ show cnt ++ " ")
            (M.assocs reprs)

printLookupeq :: (Show proof, Show (Label proof)) =>
                 Map (Label proof,[Constant]) ([proof], proof, EqBranchConst (Label proof)) -> String
printLookupeq l = "fromList [" ++ concat (intersperse "," $ map (\((l,as), (_,_,eq)) -> show (l,as) ++ ", (_,_," ++ show eq ++ ")") (M.toList l)) ++ "]"

printState :: (Show proof, Show (Label proof)) => ProblemState proof -> String
printState st =
   "\nreprs = " ++ printReprs (reprs st)
     ++ ", \nuses = " ++ show (uses st)
     ++ ", \nlookupeq = " ++ printLookupeq (lookupeq st)
-}
                                           
{- Tests -}

{-
test2 = printState $
          merges (newState ( 0, 6))
                 [Right (EqBranchConst (label "a")  [1,2] (5)),Right (EqBranchConst (label "a") [3,4] (6)), Left (EqConstConst (1) (3))]

test3 = printState $
         merges (newState (0, 6)) $ 
                [Left (EqConstConst 4 1),Left (EqConstConst 2 3),Right (EqBranchConst (label "a") [2,3,1,2] 4),Right (EqBranchConst (label "a") [2,2,3,1] 1),Right (EqBranchConst (label "b") [2,2,2,3] 0),Left (EqConstConst 4 2),Right (EqBranchConst (label "a") [4,4] 0)]
-}

{-- The High-level specification of the algorithm -}

-- the relation congTest contains the input equations:
prop_containsEqs :: (NonEmptyList Equation) -> Property
prop_containsEqs  (NonEmpty eqs) = 
  forAll (Gen.elements eqs) (uncurry (congTest eqs) . equationToTerms)

-- the relation congTest is a congruence (FIXME: should test for n-ary branches):
prop_congruence :: [Equation] -> Label -> Term -> Term -> Term -> Term -> Property
prop_congruence eqs l a a' b b' =
  congTest eqs a a' ==> congTest eqs b b' ==> congTest eqs (Branch l [a, b]) (Branch l [a', b'])

-- it's the least congruence, or equivantly, it contains only provable equations.
-- (Fixme: the statement of this property needs work.)
prop_soundness :: [Equation] -> Term -> Term -> Property
prop_soundness eqs a b = 
  isJust p ==> checkProof a b (simplProof (fromJust p))
  where p = congTestExplain eqs a b
  
{- Some lower-level invariants maintained by the algorithm -}

-- All critical pairs in the rewrite system lookupeq are trivial.
prop_criticalPairs :: [Equation] -> Property
prop_criticalPairs eqs =  monadic (flip evalState st) $ do
      pre (not (M.null (lookupeq st)))
      forAll2M (Gen.elements (M.toList $ lookupeq st))
        (\((l1,as), (_, _, EqBranchConst _ _ a)) ((l2,bs), (_, _, EqBranchConst _ _ b)) -> do
           as' <- run $ mapM find as
           a'  <- run $ find a
           bs' <- run $ mapM find bs
           b'  <- run $ find b
           pre (l1==l2 && as'==bs')
           assert (a'==b'))
   where st = merges (newState (0, 6)) eqs

-- lookupeq does not forget any of the BranchConst input equations.
prop_lookupeqNonlossy :: [Equation] -> Property
prop_lookupeqNonlossy eqs  = monadic (flip evalState st) $ do
    let (_,bcEqs) = partitionEithers eqs
    pre (not (null bcEqs))
    forAllM (Gen.elements bcEqs)
      (\(EqBranchConst l as a) -> do
        (_,as') <- run $ findExplains as
        (_,a')  <- run $ findExplain a
        case M.lookup (l,as') (lookupeq st) of
          Nothing -> assert False
          Just (_, _, EqBranchConst l' bs b) -> do
            b' <- run $ find b
            assert (l==l' && a'== b'))  
 where st = merges (newState (0, 6)) eqs


-- All proofs recorded on the Union-find arcs are valid.
prop_validProofsArcs :: [Equation] -> Property
prop_validProofsArcs eqs = monadic (flip evalState st) $ do
    forAllM (Gen.elements assocs)
      (\(a, e) -> 
         case e of
           Left (p,b) -> assert $ checkProof (Leaf a) (Leaf b) p
           Right info -> assert True)
  where st = merges (newState (0, 6)) eqs
        assocs = M.toAscList (reprs st)

-- All proofs recorded with the lookupeqs are valid.
prop_validProofsLookups :: [Equation] -> Property
prop_validProofsLookups eqs = monadic (flip evalState st) $ do
    pre (not (M.null (lookupeq st)))
    forAllM (Gen.elements (M.toList $ lookupeq st))
      (\((l,as),(ps, q, EqBranchConst _ bs b)) -> 
         assert $ and (zipWith3 checkProof (map Leaf bs) (map Leaf as) ps)
                  && checkProof (Branch l (map Leaf bs)) (Leaf b) q)
  where st = merges (newState (0, 6)) eqs

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
