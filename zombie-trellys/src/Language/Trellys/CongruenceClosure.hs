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
  fineUnion,
  inSameClass, 
  unify, -- main function, runState is run for UniM monad  
  
) where

{- This module mostly follows two papers. The congruence closure part is based on
     Robert Nieuwenhuis and Albert Oliveras, "Fast Congruence Closure and Extensions",
     Information and Computation, 205(4):557-580, April 2007.  
   Compared to that paper the main differences are:
    - The terms have n-ary branches instead of being just binary trees. This ruins the
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
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Set (Set)
import qualified Data.Set as S
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.List (intercalate)
import Data.FingerTree.PSQueue (PSQ, Binding(..), minView)
import qualified Data.FingerTree.PSQueue as PQ
import Control.Monad.Trans
import Control.Monad.State.Class
import Control.Monad.Trans.State.Strict (StateT(..))
import Control.Monad.Trans.List


import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ ( render)
-- We need to know a little bit about the ATerm datatype in order to do the occurs check.
import Language.Trellys.Syntax (ATerm, AName, Label, Proof(..), proofSize, uniVars, injectiveLabelPositions, isEqualityLabel)

--Stuff used for debugging.
import Text.PrettyPrint.HughesPJ
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
  classMembers     :: Set Constant,                     -- All elements in the class
  classUniVars     :: Set (AName,Constant),             -- All unification variables that are elements of the class; 
                                                        --    also remember which c they correspond to.
  classApps        :: Set (Label, [Constant]),          -- All applications that are elements of the class
  classInjTerm     :: Maybe (Proof, Label, [Constant], Constant),
        -- This is Just(p, l,as c)   
        -- If there is a term headed by an injective label in the class.
        -- Here, 
        --   p :  l as = c
        --  where c is some constant in the class. 
  classEquations   :: Set (Constant,Constant,Constant), -- (c,a,b) such that c is in the class and c == (a=b).
  classInhabitants :: Set (Constant,Constant)           -- (c, cTy) such that c : cTy and cTy is in the class.
                                                        --   Note we only track variables from the context here.
}

instance Show ClassInfo where
  show _ = "<classInfo>"

classSize :: ClassInfo -> Int
classSize cls = S.size (classMembers cls)

combineInfo :: ClassInfo -> ClassInfo  -> ClassInfo 
combineInfo a b =
  ClassInfo (S.union (classMembers a) (classMembers b))
            (S.union (classUniVars a) (classUniVars b))
            (S.union (classApps a) (classApps b))
            ((classInjTerm a) `orElse` (classInjTerm b))
            (S.union (classEquations a) (classEquations b))
            (S.union (classInhabitants a) (classInhabitants b))

orElse :: Maybe a -> Maybe a -> Maybe a
orElse (Just a) _ = Just a
orElse Nothing mb = mb

-- Union-Find representatives.
type Reprs = IntMap (Either Constant ClassInfo)
                                        -- (p:i=i', i')
type ExplainedEquation = (Proof, Equation)

-- We also maintain a finer equivalence relation between terms which
-- were proved equal by parallel-reductions by the unfold tactic. It
-- is used by classMembersExplain.  This lets unfold avoid wasting
-- work on ~p>-equivalent terms.
--
-- Note: the map is defined for things which are not their own representatives.
type FineReprs = IntMap Constant

data ProblemState = ProblemState {
  -- union-find structure mapping constants to their representative.
  reprs :: Reprs,

  -- also a union-find structure mapping constants to representatives
  fineReprs :: FineReprs,

  -- maps c to list of equations l(a1..an)=b such that some ai is related to c.
  uses :: Map Constant [(Proof, EqBranchConst)],

  -- maps (l, (a1..an)) to an input equation (l(b1..bn)=b) with (ai..an) representatives of (bi..vn).
  --  If as |-> (ps, q,  bs=b) then:
  --   pi : bi = ai
  --   q  : bs = b.
  lookupeq :: Map (Label,[Constant]) ([Proof], Proof, EqBranchConst),

  -- This keeps track of all known proofs of equations between constants.
  edges :: Map Constant [(Proof, Constant)],

  unboundVars :: Map AName Constant,  --The variables that can still be assigned, 
                                      -- with their (constantified) types.
  bindings    :: Map AName Constant,  --Assignment to unification variables
  proofs      :: Map WantedEquation Proof,

  -- The mapping between constants and the ATerms they denote.
  naming      :: Bimap ATerm Constant
}


-- Print out the current state of the congruence closure algorithm.
dumpState :: (MonadIO m) => ProblemState -> m ()
dumpState st = 
  --liftIO $ putStrLn $ show (reprs st)
  liftIO $ mapM_ printClass (IM.toList (reprs st))
  where showConst :: Constant -> String
        showConst c = render (disp (naming st BM.!> c))
        printClass :: (Constant, (Either Constant ClassInfo)) -> IO ()
        printClass (c, Left _) = 
          putStrLn $ "The constant " ++ showConst c ++ " is also somewhere in the map"
        printClass (_, Right info) = 
          putStrLn $ "Equivalence class:\n {"
                     ++ intercalate ", " (map showConst (S.toList $ classMembers info)) 
                     ++ "}\n"
                     ++ "has inhabitants:\n {"
                     ++ intercalate ", " (map (\(c,cTy) -> showConst c ++ " : " ++ showConst cTy) 
                                           (S.toList $ classInhabitants info))
                     ++ "}\n"
                     ++ "and contains the equations:\n {"
                     ++ intercalate ", " (map (\(c,a,b) -> showConst c)  (S.toList $ classEquations info))
                     ++ "}"

-- for debugging.
dispEdges :: Monad m => StateT ProblemState m Doc
dispEdges = do
  names <- gets naming
  graph <- gets edges
  return $
   nest 2 $ vcat  [ disp (names BM.!> a) <+> text "--->" <+> disp (names BM.!> b) $$ text " by" <+> disp p
                    | (a, outedges) <- M.toList graph, (p, b) <- outedges ]
     

-- | Allocate a constant which is not mentioned in 'reprs'.
freshConstant :: (Monad m) => StateT ProblemState m Constant
freshConstant = do
  st <- get
  if IM.null (reprs st)
     then return 0
     else case (IM.findMax (reprs st)) of
            (n,_)     -> return (n+1)

-- | Allocate a new name (Constant) for a subterm.
recordName :: (Applicative m, Monad m) => ATerm -> StateT ProblemState m Constant
recordName a = do
  existing <- BM.lookup a <$> gets naming
  case existing of 
    Just c -> 
      return c
    Nothing -> do
      c <- freshConstant
      let singletonClass = ClassInfo{ classMembers = S.singleton c,
                                      classUniVars = S.empty,
                                      classApps = S.empty,
                                      classInjTerm = Nothing,
                                      classEquations = S.empty,
                                      classInhabitants = S.empty }
      st <- get
      put (st{ reprs = IM.insert c (Right singletonClass) (reprs st),
               naming = BM.insert a c (naming st)})
      return c

-- | Record that c is a unification variable, with name x and type cTy.
recordUniVar :: (Monad m) => Constant -> AName -> Constant -> StateT ProblemState m ()
recordUniVar c x cTy = do
  (c', inf) <- findInfo c
  setRepr c' (Right inf{ classUniVars = S.insert (x,c) (classUniVars inf) })
  modify (\st -> st{ unboundVars = M.insert x cTy (unboundVars st)})

-- | Record that c is one of the inhabitants of cTy.
-- (If cTy was not already known to be inhabited, then this can yield new
--  given equations too)
recordInhabitant :: (Monad m) => Constant -> Constant -> StateT ProblemState m ()
recordInhabitant c cTy = do
  (cTy', inf) <- findInfo cTy    
  setRepr cTy' (Right inf{ classInhabitants = (c,cTy) `S.insert` classInhabitants inf})

  -- TODO: Actually, it can be worth adding it anyway, to get an additional edge in the graph.
  --when (S.null (classInhabitants inf)) $
  newAssumptions <- possiblyNewAssumptions (Just (c,cTy)) (classEquations inf)
  --mapM_ (\(p, (Left (EqConstConst a b))) -> recordEdge a b p)
  --      newAssumptions 
  propagate newAssumptions

-- | Record that c is an equation between a and b
-- (If the equivalence class of c is inhabited, this yields a new given equation too).
recordEquation :: (Monad m) => Constant -> (Constant,Constant) -> StateT ProblemState m ()
recordEquation  c (a,b) = do
  (c', inf) <- findInfo c
  setRepr c' (Right inf{ classEquations = (c,a,b) `S.insert` classEquations inf})
  newAssumptions <- possiblyNewAssumptions (someElem $ classInhabitants inf) (S.singleton (c,a,b))
  propagate newAssumptions

-- The list contains all the constants in the state, together with
--   * if the contant itself represents a variable, the name of the variable.
--   * the set of all variables that occurs in the term that the constant represents.
newState :: ProblemState
newState =
  ProblemState{reprs = IM.empty,
               fineReprs = IM.empty,
               uses = M.empty,
               lookupeq = M.empty,
               edges = M.empty,
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
setRepr :: (Monad m) => Constant -> (Either Constant ClassInfo) -> StateT ProblemState m ()
setRepr c val = modify (\st -> st{ reprs = IM.insert c val (reprs st) })

giveBinding :: (Monad m) => AName -> Constant -> StateT ProblemState m ()
giveBinding x val = modify (\st -> st{ bindings = M.insert x val (bindings st), 
                                       unboundVars = M.delete x (unboundVars st) })

giveProof :: WantedEquation -> Proof -> UniM ()
giveProof e p = modify (\st -> st{ proofs  = M.insert e p (proofs st) })

-- Returns the representative of x.
find :: Monad m => Constant -> StateT ProblemState m Constant
find x  = do
  (x', _) <- findInfo x
  return x'

findInfo :: Monad m => Constant -> StateT ProblemState m (Constant,ClassInfo)
findInfo x = do
  content <- return (IM.!) `ap` (gets reprs) `ap` return x
  case content of
    Left x' -> do
       (x'',info) <- findInfo x'
       if x'' /= x' 
         then do
           setRepr x (Left x'') --path compression.
           return (x'', info)
         else 
           return (x',info)
    Right info  -> return (x, info)

-- Given a constant, return all the constants in its equivalence class,
--  and a proof that they are equal.
-- Actually it's not all the constants, because we only return one representative from
-- each "fine" equivalence class.
classMembersExplain :: Monad m => Constant -> StateT ProblemState m [(Constant, Proof)]
classMembersExplain x = do
  (_x', xinfo) <- findInfo x
  runListT $ do
    y <- ListT . return . S.toList $ classMembers xinfo
    y' <- lift $ find y
    y'' <- lift $ fineFind y   
    guard (y == y'')   --filter out duplicates from the same fine class.
    pf <- lift $ proveEqual x y
    return $ (y, pf)


recordEdge :: Monad m => Constant -> Constant -> Proof -> StateT ProblemState m ()
recordEdge x y p = do
  modify (\st -> st{ edges = M.insertWith (++) x [(p, y)] (edges st) })
  modify (\st -> st{ edges = M.insertWith (++) y [(RawSymm p, x)] (edges st) })

-- Returns the old representative of the smaller class.
-- Note: any time you call union you must all so call recordEdge. 
-- (But it is fine to add more edges between constants that already in the same union-find class)
union :: Monad m => Constant -> Constant -> Proof -> StateT ProblemState m Constant
union x y p = do
  (x', xinfo) <- findInfo x 
  (y', yinfo) <- findInfo y
  if (classSize xinfo) < (classSize yinfo)
    then do
           setRepr x' (Left y')
           setRepr y' (Right $ (xinfo `combineInfo` yinfo))
           return x'
    else do
           setRepr y' (Left x')
           setRepr x' (Right $ (xinfo `combineInfo` yinfo))
           return y'

-- A path is a list of equality proofs (to be chained by transitivity).
type Cost = Int
data BestPath =
    Path Cost [Proof]   --NB, the list is built in reverse order...
  | NoPath
 deriving (Eq, Show)

-- Ord compares cost. NoPath is infinitely costly.
instance Ord BestPath where
  compare NoPath NoPath = EQ
  compare NoPath _ = GT
  compare _ NoPath = LT
  compare (Path c1 _) (Path c2 _) = compare c1 c2

extend :: Cost -> Proof -> BestPath -> BestPath
extend k p (Path k' ps) = Path (k+k') (p:ps)
extend _ _ NoPath = NoPath


-- Returns a proof that x and y are equal. 
-- Precondition: they must be in the same union-find class.
-- We search for the shortest path in the 'edges' graph.
proveEqual :: Monad m => Constant -> Constant -> StateT ProblemState m Proof
proveEqual x y | x==y = return RawRefl
proveEqual x y = do
  theGraph <- gets edges
  let dijkstra :: Constant -> PSQ Constant BestPath  -> BestPath
      dijkstra goal (minView -> Nothing) = NoPath
      dijkstra goal (minView -> Just((n :-> path), _)) | n==goal = path
      dijkstra goal (minView -> Just((n :-> path), rest)) =  dijkstra goal (visit rest)
       where visit :: PSQ Constant BestPath -> PSQ Constant BestPath
             visit unvisited = foldr (\(p', n') uv -> PQ.adjust (min (extend (proofSize p') p' path)) n' uv)
                                     unvisited
                                     (M.findWithDefault [] n theGraph)
  -- Unvisited starts out with the source node having cost 0, and all the rest cost Infinity:
  let initialUnvisited =   PQ.fromList [(n :-> path) | n <- (M.keys theGraph),
                                                       let path = if (n==x) then (Path 0 []) else NoPath]                      
  case dijkstra y initialUnvisited of 
    NoPath -> error "Internal error: proveEqual found no path"
    Path _ ps -> return $ foldr RawTrans RawRefl (reverse ps)

-- Add an application term to the equivalence class of a constant
recordApplication :: (Monad m) => Constant -> (Label, [Constant]) 
                     -> StateT ProblemState m ()
recordApplication a app = do
  (a',ia) <- findInfo a
  setRepr a' (Right $ ia{ classApps = S.insert app (classApps ia)})

-- Add an application term to the injTerm field of an equivalence class of a constant
recordInjTerm :: (Monad m) =>  Constant -> (Proof, Label, [Constant], Constant) 
                     -> StateT ProblemState m ()
recordInjTerm a app = do
  (a',ia) <- findInfo a
  setRepr a' (Right $ ia{ classInjTerm = (classInjTerm ia) `orElse` (Just app) })

-- Called when we have just unified two equivalence classes. If both classes contained
-- an injective term, we return the list of new equations.
-- Preconditions: the labels should be injective, the two terms should be equal.
possiblyInjectivity :: (Monad m) => Maybe (Proof, Label, [Constant], Constant) 
                                 -> Maybe (Proof, Label, [Constant], Constant) ->
                       StateT ProblemState m [ExplainedEquation]
possiblyInjectivity (Just (p, l1, as, a)) (Just (q, l2, bs, b)) | l1/=l2 = do
  -- todo: register that we found a contradiction
  return []
possiblyInjectivity (Just (p, l, as, a)) (Just (q, l2, bs, b)) | l==l2 = do
  r <- proveEqual a b
  let pf = RawTrans p (RawTrans r (RawSymm q)) {- : l(as) = l(bs) -}
  return $ zipWith3 (\ i lhs rhs -> (RawInj i pf, Left (EqConstConst lhs rhs)))
                    (injectiveLabelPositions l)
                    as
                    bs
possiblyInjectivity _ _ = return []

-- Called when we have just unified two equivalence classes. 
-- If one of the classes contained an assumption variable and 
-- the other contains equations, we return the list of new equations
--
-- Note we do not check that the equations were not already known. 
-- If the generated equations are redundant we will notice later, in propagate.
possiblyNewAssumptions :: Monad m => Maybe (Constant,Constant) -> Set (Constant,Constant,Constant) -> 
                          StateT ProblemState m [ExplainedEquation]
possiblyNewAssumptions  Nothing _ = return []
possiblyNewAssumptions  (Just (c1Inhabitant,c1)) qs =  mapM possiblyNewAssumption $ S.elems qs
 where possiblyNewAssumption (c2,a,b) = do
         names <- gets naming
         p <- proveEqual c1 c2
         return (RawAssumption (names BM.!> c1Inhabitant, p), 
                 Left (EqConstConst a b))

someElem :: Set a -> Maybe a
someElem s | S.null s = Nothing
           | otherwise = Just (S.findMin s)

isAssumption :: Proof -> Bool
isAssumption (RawAssumption _) = True
isAssumption _ = False 

-- propagate takes a list of given equations, and constructs the congruence
-- closure of those equations.
propagate :: Monad m => [ExplainedEquation] -> StateT ProblemState m ()
propagate ((p, Left (EqConstConst a b)):eqs) = do
  (ar, ia) <- findInfo a
  (br, ib) <- findInfo b

  {- We should be able to get shorter proofs by not throwing away assumptions?
     But it slows everything down a lot.
  when (ar==br && a/=b && isAssumption p) $ do    
    recordEdge a b p -}
  if ar /= br  --if not already in the same union-find class
    then do
      recordEdge a b p
      a' <- union a b p
      a_uses <- M.findWithDefault [] a' `liftM` (gets uses)
      injections <- possiblyInjectivity (classInjTerm ia) (classInjTerm ib)
      newAssumptions1 <- possiblyNewAssumptions (someElem $ classInhabitants ia) (classEquations ib)
      newAssumptions2 <- possiblyNewAssumptions (someElem $ classInhabitants ib) (classEquations ia)
      propagate (map (\(q,eq) -> (q, (Right eq))) a_uses ++ injections ++ newAssumptions1 ++ newAssumptions2 ++ eqs)
   else 
      propagate eqs
propagate ((p, Right eq_a@(EqBranchConst l as a)):eqs) = do
  recordApplication a (l,as)
  when (injectiveLabelPositions l /= []) $ 
    recordInjTerm a (p,l,as,a)  
  when (isEqualityLabel l) $
    recordEquation a ((as!!0), (as!!1))
  as' <- mapM find as
  lookupeqs <- gets lookupeq
  case M.lookup (l, as') lookupeqs of
    Just (qs, q, eq_b@(EqBranchConst _ bs b)) ->  do
      (_,ia) <- findInfo a
      (_,ib) <- findInfo b
      -- Todo: do we need this injections? We can't call possiblyInjectivity here, because we
      --   have not yet done the union. But we will do the union very soon.
      --   Similarly, if we have a possiblyInjectivity we presumably need a possiblyAssumptions too?
      --injections <- possiblyInjectivity (classInjTerm ia) (classInjTerm ib)

      rs <- zipWithM proveEqual as bs
      let r = RawTrans (RawSymm p) 
                       --(Branch l (map Leaf as))
                       (RawTrans (RawCong l rs)
                              --(Branch l (map Leaf bs))
                              q)

      propagate ((r, Left (EqConstConst a b)):eqs)
    Nothing -> do
      ps <- zipWithM proveEqual as as'
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
  a' <- find a
  b' <- find b
  guard (a' == b')
  r <- proveEqual a b
  giveProof (WantedEquation a b) r
 
  {- 
  graph <- dispEdges
  trace (render (text "The graph is:" $$ graph)) (return ()) 
  -}

  tracing "Deleted" (WantedEquation a b) (return ())

-- If the lhs of a wanted equation is an evar, instantiate it with the rhs.
unifyBind :: WantedEquation -> UniM  ()
unifyBind  (WantedEquation a b) = do
  (_, ia) <- findInfo a
  (_, ib) <- findInfo b
  unbounds <- gets unboundVars
  names <- gets naming
  (x,c) <- lift (S.toList $ classUniVars ia)
  guard (x `M.member` unbounds)
  -- Don't backtrack over which member of the equivalence class gets picked.
  d <- cut $ do
    --if possible we prefer picking b itself, for simpler equality proofs.
    d <- lift (b : (S.toList $ classMembers ib))
    guard $ not (x `S.member` uniVars (names BM.!> d))-- occurs check
-- This typing check (following two lines) fails for an interesting reason (see comment about Product.trellys in notes.tex)
  --  namesTy <- gets namingTy
  --    let xTy = names BM.!> (unbounds M.! x)
  --    guard $ (namesTy IM.! d) `aeq` xTy -- typing check
{-
    trace (render . disp $ [ DS "The equivalence class of b contains"]
             ++ map (DD . (names BM.!>)) (S.toList $ classMembers ib)
             ++ [DS "the unification variable had type", DD xTy, 
                 DS "although that is not currently being taken into account."]
             ++ [DS "We pick", DD (names BM.!> d)]) $ return ()
-}
    return d
  giveBinding x d
  propagate [(RawRefl, Left $ EqConstConst c b)]
  --Now the equation ought to be trivial:
  unifyDelete (WantedEquation a b)
  tracing "Bound" (WantedEquation a b) (return ())

-- If both sides of the equation are applications headed by the same label, try to unify the args.
unifyDecompose :: Set WantedEquation -> WantedEquation -> UniM ()
unifyDecompose visited (WantedEquation a b) = do
  (_, ia) <- findInfo a
  (_, ib) <- findInfo b
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
  tracing "Considering" (WantedEquation a b) (return ())

  guard (not (S.member (WantedEquation a b) visited))
  unifyDelete (WantedEquation a b)
   `mplusCut`
   unifyBind (WantedEquation a b)
   `mplusCut` 
   (do unifyBind (WantedEquation b a) ; unifyDelete (WantedEquation a b))
   `mplusCut`
   unifyDecompose visited (WantedEquation a b)
  unify visited wanted

inSameClass :: (Monad m) => Constant -> Constant -> StateT ProblemState m Bool
inSameClass c1 c2 = do
  c1' <- find c1
  c2' <- find c2
  return (c1' == c2')

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
           (_, inf) <- findInfo xTy
           -- liftIO $ putStrLn $ "Trying to decide what to pick for " ++ show x
           -- liftIO $ putStrLn $ "The set of inhabitants is: "
           --                      ++ intercalate ", "  (map (render . disp . (names BM.!>))
           --                                                (S.toList $ classInhabitants inf))
           let candidates = [ c | (c,_cTy) <- (S.toList $ classInhabitants inf), 
                                  S.null (uniVars (names BM.!> c)) ] --huge hack.
--                                not (x `S.member` uniVars (names BM.!> c)) ] --occurs check
           when (null candidates) $
             liftIO $ putStrLn . render . disp $ [ DS "Oops, no candidates for guessing the variable", DD x, DS  "of type",
                                                   DD (names BM.!> xTy)]
           guard (not $ null candidates)
           let a = head $ candidates
           liftIO $ putStrLn $ "Setting a var of type ("
                                ++ render (disp (names BM.!> xTy))
                                ++ ") to be ("
                                ++ render (disp (names BM.!> a))
                                ++ ")."
           giveBinding x a)
        
----------------------------------------------------------------
-- Maintaining the "fine" equivalence relation

fineFind :: Monad m => Constant -> StateT ProblemState m Constant
fineFind x = do
  content <- return (IM.lookup) `ap` return x `ap` (gets fineReprs)
  case content of
    Just x' -> do
       x'' <- fineFind x'
       modify (\st -> st{ fineReprs = IM.insert x x'' (fineReprs st) })
       return x''
    Nothing -> return x

-- Perhaps somewhat confusingly, this is an asymmetric operation.
-- (fineUnion a a') means "a simplifies to a', so always prefer a' over a".
fineUnion :: Monad m => Constant -> Constant -> StateT ProblemState m ()
fineUnion x y = do
  y' <- fineFind y
  modify (\st -> st{ fineReprs = IM.insert x y' (fineReprs st) })





