{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, TypeFamilies, 
             FlexibleInstances, FlexibleContexts, ViewPatterns,
             TemplateHaskell, RankNTypes #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.CongruenceClosure(
 Constant, EqConstConst(..), EqBranchConst(..), Equation, WantedEquation(..),
 Proof(..),
  ProblemState, proofs, bindings, naming,
  newState, freshConstant, propagate, 
  recordName, recordInhabitant, recordUniVar,
  guessVars, classMembersExplain,
  dumpState,
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
import Data.Map (Map)
import qualified Data.Map as M
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Set (Set)
import qualified Data.Set as S
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.List (intercalate)
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict
-- We need to know a little bit about the ATerm datatype in order to do the occurs check.
import Language.Trellys.Syntax (ATerm, AName, Label, Proof(..), uniVars)

--Stuff used for debugging.
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ ( (<>), (<+>),hsep,text, parens, brackets, nest, render)
import Debug.Trace

type Constant = Int

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
  classMembers     :: Set Constant,            -- All elements in the class
  classVars        :: Set (AName,Constant),    -- All variables that are elements of the class; 
                                                 ---  also remember which c they correspond to.
  classApps        :: Set (Label, [Constant]), -- All applications that are elements of the class
  classInhabitants :: Set Constant             -- Constants whose type is this constant. 

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
            (S.union (classInhabitants a) (classInhabitants b))

-- Union-Find representatives.
type Reprs = IntMap (Either (Proof, Constant) ClassInfo)
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

  unboundVars :: Map AName Constant,  --The variables that can still be assigned, 
                                         -- with their types.
  bindings    :: Map AName Constant,  --Assignment to unification variables
  proofs      :: Map WantedEquation Proof,

  -- Recall the mapping between constants and the ATerms they denote.
  naming      :: Bimap ATerm Constant
}


-- Print out the current state of the congruence closure algorithm.
dumpState :: (MonadIO m) => ProblemState -> m ()
dumpState st = 
  --liftIO $ putStrLn $ show (reprs st)
  liftIO $ mapM_ printClass (IM.toList (reprs st))
  where showConst :: Constant -> String
        showConst c = render (disp (naming st BM.!> c))
        printClass :: (Constant, (Either (Proof, Constant) ClassInfo)) -> IO ()
        printClass (c, Left _) = 
          putStrLn $ "The constant " ++ showConst c ++ " is also somewhere in the map"
        printClass (_, Right info) = 
          putStrLn $ "Equivalence class:\n {"
                     ++ intercalate ", " (map showConst (S.toList $ classMembers info)) 
                     ++ "}\n"
                     ++ "has inhabitants:\n {"
                     ++ intercalate ", " (map showConst (S.toList $ classInhabitants info)) 
                     ++ "}"

-- | Allocate a constant which is not mentioned in 'reprs'.
freshConstant :: (Monad m) => StateT ProblemState m Constant
freshConstant = do
  st <- get
  if IM.null (reprs st)
     then return 0
     else case (IM.findMax (reprs st)) of
            (n,_)     -> return (n+1)

-- | Allocate a new name (Constant) for a subterm.
-- Note that (AType l) is treated specially, to avoid infinite regress.
-- TODO: maybe we don't need to treat it specially after all?
recordName :: (Applicative m, Monad m) => ATerm -> StateT ProblemState m Constant
recordName a = do
  existing <- BM.lookup a <$> gets naming
  case existing of 
    Just c -> 
      return c
    Nothing -> do
      c <- freshConstant
      let singletonClass = ClassInfo{ classMembers = S.singleton c,
                                      classVars = S.empty,
                                      classApps = S.empty,
                                      classInhabitants = S.empty }
      st <- get
      put (st{ reprs = IM.insert c (Right singletonClass) (reprs st),
               naming = BM.insert a c (naming st) })
      return c

-- | Record that c is a unification variable, with name x and type cTy.
recordUniVar :: (Monad m) => Constant -> AName -> Constant -> StateT ProblemState m ()
recordUniVar c x cTy = do
  (_, c', inf) <- findExplainInfo c
  setRepr c' (Right inf{ classVars = S.insert (x,c) (classVars inf) })
  modify (\st -> st{ unboundVars = M.insert x cTy (unboundVars st)})

-- | Record that c is one of the inhabitants of cTy.
recordInhabitant :: (Monad m) => Constant -> Constant -> StateT ProblemState m ()
recordInhabitant c cTy = do
  (_, cTy', inf) <- findExplainInfo cTy
  setRepr cTy' (Right inf{ classInhabitants = c `S.insert` classInhabitants inf})

-- The list contains all the constants in the state, together with
--   * if the contant itself represents a variable, the name of the variable.
--   * the set of all variables that occurs in the term that the constant represents.
newState :: ProblemState
newState =
  ProblemState{reprs = IM.empty,
               uses = M.empty,
               lookupeq = M.empty,
               unboundVars = M.empty,
               bindings = M.empty,
               proofs = M.empty,
               naming = BM.empty}

-- Most unification functions live inside a monad:
--  state to keep track of the problem state, plus list for making nondeterministic choices.
--
-- The Union-Find structure does not do any backtracking, so those functions are more polymorphic
-- and live in (Monad m) => (StateT (ProblemState proof) m).
type UniM a = StateT ProblemState [] a

-- Sets the union-find representative
setRepr :: (Monad m) => Constant -> (Either (Proof, Constant) ClassInfo) -> StateT ProblemState m ()
setRepr c val = modify (\st -> st{ reprs = IM.insert c val (reprs st) })

giveBinding :: (Monad m) => AName -> Constant -> StateT ProblemState m ()
giveBinding x val = modify (\st -> st{ bindings = M.insert x val (bindings st), 
                                       unboundVars = M.delete x (unboundVars st) })

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
  content <- return (IM.!) `ap` (gets reprs) `ap` return x
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

{-
tracing :: String -> WantedEquation -> UniM a -> UniM a
tracing msg (WantedEquation c1 c2) a = do
  names <- gets naming
  trace (msg ++ " "    ++ (render (parens (disp (names BM.!> c1))))
               ++ " == " ++ (render (parens (disp (names BM.!> c2)))))
        a
-}

tracing :: String -> WantedEquation -> UniM a -> UniM a
tracing msg eq = id

-- If a wanted equation is already in the congruence closure we can discard it.
unifyDelete :: WantedEquation -> UniM ()
unifyDelete (WantedEquation a b) = do
  (p, a', ia) <- findExplainInfo a
  (q, b', ib) <- findExplainInfo b
  guard (a' == b')
  giveProof (WantedEquation a b) (RawTrans p (RawSymm q))
  tracing "Deleted" (WantedEquation a b) (return ())

-- If the lhs of a wanted equation is an evar, instantiate it with the rhs.

-- This is hacky, way to nondeterministic, fix later
unifyBind :: WantedEquation -> UniM  ()
unifyBind  (WantedEquation a b) = do
  (_, _, ia) <- findExplainInfo a
  (_, _, ib) <- findExplainInfo b
  unbounds <- gets unboundVars
  names <- gets naming
  (x,c) <- lift (S.toList $ classVars ia)
  guard (x `M.member` unbounds)
  let xTy = unbounds M.! x
  (_,_,xTyInfo) <- (findExplainInfo xTy)
  -- Don't backtrack over which member of the equivalence class gets picked.
  d <- cut $ do
    --if possible we prefer picking b itself, for simpler equality proofs.
    d <- lift (b : (S.toList $ classMembers ib))
    guard $ not (x `S.member` uniVars (names BM.!> d))-- occurs check
    guard $ d `S.member` (classInhabitants xTyInfo) -- typing check
    return d
  {-  trace (render . disp $ [ DS "The equivalence class of b contains"]
             ++ map (DD . (names BM.!>)) (S.toList $ classMembers ib)
             ++ [DS "In addition, we need something of type", DD (names BM.!> xTy),
                 DS "so the candidates are"]
             ++ map (DD . (names BM.!>)) (S.toList $ classInhabitants xTyInfo)
             ++ [DS "We pick", DD (names BM.!> d)]) $ -}
  giveBinding x d
  propagate [(RawRefl, Left $ EqConstConst c b)]
  --Now the equation ought to be trivial:
  unifyDelete (WantedEquation a b)
  tracing "Bound" (WantedEquation a b) (return ())

{-
unifyBind :: WantedEquation -> UniM  ()
unifyBind  (WantedEquation a b) = do
  (_, _, ia) <- findExplainInfo a
  (_, _, ib) <- findExplainInfo b
  unbounds <- gets unboundVars
  names <- gets naming
  let candidates = [ (x,c) | (x,c) <- (S.toList $ classVars ia), 
                             (x `M.member` unbounds),
                             let xTy = unbounds M.! x, 
                             (_,_,xTyInfo) <- lift (findExplainInfo xTy),
                             --if possible we prefer picking b itself.
                             d <- b:(S.toList $ classMembers ib),  
                             not (x `S.member` uniVars (names BM.!> d)) ] --occurs check
  guard $ not (null candidates) 
  let (x,c):_ = candidates    --If there are several variables, we don't care which one gets picked.
  giveBinding x b
  propagate [(RawRefl, Left $ EqConstConst c b)]
  --Now the equation ought to be trivial:
  unifyDelete (WantedEquation a b)
  tracing "Bound" (WantedEquation a b) (return ())
-}
-- If both sides of the equation are applications headed by the same label, try to unify the args.
unifyDecompose :: Set WantedEquation -> WantedEquation -> UniM ()
unifyDecompose visited (WantedEquation a b) = do
  (p, _, ia) <- findExplainInfo a
  (q, _, ib) <- findExplainInfo b
  (fa, as) <- lift $ S.toList $ classApps ia
  (fb, bs) <- lift $ S.toList $ classApps ib
  guard (fa == fb)
  tracing "About to Decompose" (WantedEquation a b) $ do
    unify (S.insert (WantedEquation a b) visited) (zipWith WantedEquation as bs)
    -- Now the equation should be trivial:
    unifyDelete (WantedEquation a b)
    return ()
  tracing "Decomposed" (WantedEquation a b) (return ())

-- Unify takes a list of wanted equations, and makes assignments to unification
-- variables to make all the equations true.
-- It also tracks a set of "visited" equations (think depth-first-search) in order to
-- not get stuck in a loop.
unify ::  Set WantedEquation -> [WantedEquation] -> UniM ()
unify visited [] = return ()
unify  visited (WantedEquation a b : wanted) = do
  guard (not (S.member (WantedEquation a b) visited))
  unifyDelete (WantedEquation a b)
   `mplusCut`
   unifyBind (WantedEquation a b)
   `mplusCut` 
   (do unifyBind (WantedEquation b a) ; unifyDelete (WantedEquation a b))
   `mplusCut`
   unifyDecompose visited (WantedEquation a b)
  unify visited wanted

-- | Take all remaining unbound variables, and just fill them in with any random
--   term from the context.
--
-- This function is a temporary hack. Eventually unification and guessing should be 
--  unified into a single constraint system.
guessVars :: (Monad m, MonadPlus m, MonadIO m) => StateT ProblemState m ()
guessVars = do
  names <- gets naming
  unbounds <- gets unboundVars
  forM_ (M.toList unbounds)
        (\(x, xTy) -> do
           (p, _, inf) <- findExplainInfo xTy
           -- liftIO $ putStrLn $ "Trying to decide what to pick for " ++ show x
           -- liftIO $ putStrLn $ "The set of inhabitants is: "
           --                      ++ intercalate ", "  (map (render . disp . (names BM.!>))
           --                                                (S.toList $ classInhabitants inf))
           let candidates = [ c | c <- (S.toList $ classInhabitants inf), 
                                  S.null (uniVars (names BM.!> c)) ] --huge hack.
--                             not (x `S.member` uniVars (names BM.!> c)) ] --occurs check
           guard (not $ null candidates)
           let a = head $ candidates
           liftIO $ putStrLn $ "Setting a var of type ("
                                ++ render (disp (names BM.!> xTy))
                                ++ ") to be ("
                                ++ render (disp (names BM.!> a))
                                ++ ")."
           giveBinding x a)
        