{- These tests no longer work, since they assume a different term language,
    at some point in my copious spare time I should fix this up.... -}

import Data.Bimap (Bimap)
import qualified Data.Bimap as BM

import System.IO.Unsafe
import Test.QuickCheck
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
  in flip evalState (newState (Constant 0, cmax)) $ do
       propagate (   map (\eq -> (Assumption eq, eq)) eqs 
                  ++ map (\eq -> (Refl (fst (equationToTerms (Right eq))), Right eq)) eqsAB)
       fmap (substDefnsExplanation naming) <$> isEqual acnst bcnst

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

merges :: ProblemState Explanation -> [Equation TermLabel] -> (ProblemState Explanation)
merges st eqs = execState (propagate [(Assumption eq, eq) | eq <- eqs]) st

-- Printing algorithm-state for debugging purposes:
printReprs :: (Show proof) => Reprs proof -> String
printReprs reprs = do
  concatMap (\(i, cnt) -> "\n" ++ show i ++ " => " ++ show cnt ++ " ")
            (M.assocs reprs)


printLookupeq :: (Show proof, Show (Label proof)) =>
                 Map (Label proof,[Constant]) ([proof], proof, EqBranchConst (Label proof)) -> String
printLookupeq l = "fromList [" ++ concat (List.intersperse "," $ map (\((l,as), (_,_,eq)) -> show (l,as) ++ ", (_,_," ++ show eq ++ ")") (M.toList l)) ++ "]"

printState :: (Show proof, Show (Label proof)) => ProblemState proof -> String
printState (ProblemState reprs uses lookupeq) =
   "\nreprs = " ++ printReprs reprs
     ++ ", \nuses = " ++ show uses
     ++ ", \nlookupeq = " ++ printLookupeq lookupeq
                                           
{- Tests -}

test2 = printState $
          merges (newState (Constant 0, Constant 6))
                 [Right (EqBranchConst (TermLabel "a")  [Constant 1,Constant 2] (Constant 5)),Right (EqBranchConst (TermLabel "a") [Constant 3,Constant 4] (Constant 6)), Left (EqConstConst (Constant 1) (Constant 3))]

test3 = printState $
         merges (newState (Constant 0, Constant 6)) $ 
                [Left (EqConstConst 4 1),Left (EqConstConst 2 3),Right (EqBranchConst (TermLabel "a") [2,3,1,2] 4),Right (EqBranchConst (TermLabel "a") [2,2,3,1] 1),Right (EqBranchConst (TermLabel "b") [2,2,2,3] 0),Left (EqConstConst 4 2),Right (EqBranchConst (TermLabel "a") [4,4] 0)]

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
   where st = merges (newState (Constant 0, Constant 6)) eqs

-- lookupeq does not forget any of the BranchConst input equations.
prop_lookupeqNonlossy :: [Equation TermLabel] -> Property
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
 where st = merges (newState (Constant 0, Constant 6)) eqs


-- All proofs recorded on the Union-find arcs are valid.
prop_validProofsArcs :: [Equation TermLabel] -> Property
prop_validProofsArcs eqs = monadic (flip evalState st) $ do
    forAllM (Gen.elements assocs)
      (\(a, e) -> 
         case e of
           Left (p,b) -> assert $ checkExplanation (Leaf a) (Leaf b) p
           Right info -> assert True)
  where st = merges (newState (Constant 0, Constant 6)) eqs
        assocs = M.toAscList (reprs st)

-- All proofs recorded with the lookupeqs are valid.
prop_validProofsLookups :: [Equation TermLabel] -> Property
prop_validProofsLookups eqs = monadic (flip evalState st) $ do
    pre (not (M.null (lookupeq st)))
    forAllM (Gen.elements (M.toList $ lookupeq st))
      (\((l,as),(ps, q, EqBranchConst _ bs b)) -> 
         assert $ and (zipWith3 checkExplanation (map Leaf bs) (map Leaf as) ps)
                  && checkExplanation (Branch l (map Leaf bs)) (Leaf b) q)
  where st = merges (newState (Constant 0, Constant 6)) eqs

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
