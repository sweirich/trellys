{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    GeneralizedNewtypeDeriving, ViewPatterns,
    UndecidableInstances, OverlappingInstances, TypeSynonymInstances, 
    TupleSections, TypeFamilies, GADTs, DataKinds #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

module Language.Trellys.EqualityReasoning 
  (underHypotheses, prove, solveConstraints, uneraseEq, smartSteps, 
   intoArrow, intoTCon, outofArrow, outofTyEq, injRngFor)
where

import Language.Trellys.TypeMonad
import Language.Trellys.Syntax
import Language.Trellys.Environment(setUniVars, lookupUniVar,
                                   Constraint(..), getConstraints, clearConstraints,
                                   extendCtx,
                                   warn, err, 
                                   zonkTerm, zonkWithBindings)
import Language.Trellys.OpSem(erase, eraseToHead)
import Language.Trellys.AOpSem (astep)
import Language.Trellys.TypeCheckCore (aGetTh, getType)
import Language.Trellys.CongruenceClosure

import Language.Trellys.GenericBind hiding (avoid)

import Control.Applicative 
import Control.Monad.Writer.Lazy (WriterT, runWriterT, tell )
import Control.Monad.State.Strict
import Control.Monad.Error.Class
--import Data.Foldable (foldrM)
--mport Data.List (partition, sortBy)
import Data.Maybe (fromJust,isNothing)
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.Function (on)
import Text.PrettyPrint.HughesPJ (render)
import Debug.Trace

--Stuff used for debugging.
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ ((<+>),hsep,text, parens, vcat, colon)
{-
import Language.Trellys.TypeCheckCore (aTs)
-}

-- In the decompose function, we will need to "canonicalize" certain fields
-- that should not matter in the erased language. For readability we use
-- this typeclass

class Canonical a where
  canonical :: a

instance Canonical Theta where
  canonical = Logic

instance Canonical Int where
  canonical = 0

instance Canonical EvaluationStrategy where
  canonical = CBV

instance Canonical Explicitness where
  canonical = Explicit

instance Canonical ATerm where
   canonical = AVar (string2Name "erased")

-- ********** ASSOCIATION PHASE 
-- In a first pass, we associate all uses of trans to the right, which
-- lets us simplify subproofs of the form (trans h (trans (symm h) p))
-- to just p. (This is done by the rawTrans helper function).
-- This is important because such ineffecient proofs are
-- often introduced by the union-find datastructure.

associateProof :: Proof -> Proof
associateProof (RawAssumption h) = RawAssumption h
associateProof RawRefl = RawRefl
associateProof (RawSymm p) = case associateProof p of
                               RawRefl -> RawRefl
                               p'      -> RawSymm p'
associateProof (RawTrans p q) = rawTrans (associateProof p) (associateProof q)
associateProof (RawCong l ps) = RawCong l (map associateProof ps)
associateProof (RawInj i p) = RawInj i (associateProof p)

-- This is a smart constructor for RawTrans
rawTrans :: Proof -> Proof -> Proof
rawTrans RawRefl p = p
rawTrans p RawRefl = p
rawTrans (RawTrans p q) r = maybeCancel p (rawTrans q r)
rawTrans p q = RawTrans p q
--where
maybeCancel :: Proof -> Proof -> Proof
maybeCancel p           (RawTrans (RawSymm q) r) | p==q = r
maybeCancel (RawSymm p) (RawTrans q r)           | p==q = r
maybeCancel p q = RawTrans p q


-- ********** SYMMETRIZATION PHASE
-- Next we simplify the Proofs into Raw1Proofs, which gets rid of
-- the Symm constructor by pushing it up to the leaves of the tree.

data Orientation = Swapped | NotSwapped
  deriving (Show,Eq)
data Raw1Proof =
   Raw1Assumption Orientation (ATerm, Raw1Proof)
 | Raw1Refl
 | Raw1Trans Raw1Proof Raw1Proof
 | Raw1Cong Label [Raw1Proof]
 | Raw1Inj Int Raw1Proof
  deriving Show

flipOrientation :: Orientation -> Orientation
flipOrientation Swapped = NotSwapped
flipOrientation NotSwapped = Swapped

symmetrizeProof :: Proof -> Raw1Proof
symmetrizeProof (RawAssumption (h,p)) = Raw1Assumption NotSwapped (h,symmetrizeProof p)
symmetrizeProof (RawSymm (RawAssumption (h,p))) = Raw1Assumption Swapped  (h, symmetrizeProof p)
symmetrizeProof RawRefl = Raw1Refl
symmetrizeProof (RawSymm RawRefl) = Raw1Refl
symmetrizeProof (RawSymm (RawSymm p)) = symmetrizeProof p
symmetrizeProof (RawTrans p q) = Raw1Trans (symmetrizeProof p) (symmetrizeProof q)
symmetrizeProof (RawSymm (RawTrans p q)) = Raw1Trans (symmetrizeProof (RawSymm q))
                                                     (symmetrizeProof (RawSymm p))
symmetrizeProof (RawCong l ps) = Raw1Cong l (map symmetrizeProof ps)
symmetrizeProof (RawSymm (RawCong l ps)) = Raw1Cong l (map (symmetrizeProof . RawSymm) ps)
symmetrizeProof (RawInj i p) = Raw1Inj i (symmetrizeProof p)
symmetrizeProof (RawSymm (RawInj i p)) = Raw1Inj i (symmetrizeProof (RawSymm p))

-- ********** NORMALIZATION PHASE
--  The raw1 proof terms are then normalized into this datatype, by
-- associating transitivity to the right and fusing adjacent Congs.  A
-- SynthProof lets you infer the equality it is proving, while a
-- CheckProof doesn't.

data SynthProof =
    Assum Orientation (ATerm,ChainProof) 
  | Inj Int SynthProof
  | Chain ChainProof  --Extra invariant: both ends of the chain should be definite.

data CheckProof =
   Cong ATerm [(AName, ChainProof)]

-- This type additionally maintains the invariant that there are 
-- never two CheckProofs next to each other, but I don't formalize 
-- that in the type system (too fiddly).
type ChainProof = [Either SynthProof CheckProof]

deriving instance Show SynthProof
deriving instance Show CheckProof

--Applying symmetry to a synth/check/chainproof.
symmSynthProof :: SynthProof -> SynthProof
symmSynthProof (Assum o h) = Assum (flipOrientation o) h
symmSynthProof (Inj i p) = Inj i (symmSynthProof p)
symmSynthProof (Chain ps) = Chain (symmChainProof ps)

symmCheckProof :: CheckProof -> CheckProof
symmCheckProof (Cong templ ps) = Cong templ $ map (\(x,p)->(x, symmChainProof p)) ps

symmChainProof :: ChainProof -> ChainProof
symmChainProof = reverse . map (either (Left . symmSynthProof) (Right . symmCheckProof))

transProof :: ChainProof -> ChainProof -> ChainProof
transProof ps0 qs0 = foldr trans1Proof qs0 ps0
 where trans1Proof :: (Either SynthProof CheckProof) -> ChainProof -> ChainProof
       trans1Proof (Right (Cong l ps)) (Right (Cong _ ps') : qs) =
           Right (Cong l (zipWith transSubproof ps ps')) : qs
       trans1Proof p qs = p : qs
       transSubproof :: (AName, ChainProof) -> (AName,  ChainProof) -> (AName, ChainProof)
       transSubproof (x,p)  (_,q)  = (x, transProof p q)

flatMapProof :: (a -> ChainProof) -> [a] -> ChainProof
flatMapProof f (a:as) = transProof (f a) (flatMapProof f as)
flatMapProof f [] = []

injProof :: Int -> ChainProof -> ChainProof
injProof i ps =
  let (prefix :: [CheckProof], ps') = takeWhileRight ps
      (reverse -> end :: [CheckProof], reverse -> middle :: ChainProof) = takeWhileRight (reverse ps')
  in transProof (flatMapProof (injCong i) prefix) 
                (Left (Inj i (Chain middle)) : flatMapProof (injCong i) end)

injCong :: Int -> CheckProof  -> ChainProof
injCong i (Cong l ps) = snd (ps !! i)

takeWhileRight :: [Either a b] -> ([b], [Either a b])
takeWhileRight [] = ([],[])
takeWhileRight (Right x : xs) = let (ys,zs) = takeWhileRight xs in (x:ys, zs)
takeWhileRight xs@(Left _ : _) = ([],xs)

fuseProof :: (Applicative m, Fresh m)=> Raw1Proof -> m ChainProof
fuseProof (Raw1Assumption o (h,p)) = do
    p' <- fuseProof p
    -- p' is fused, so it ends with either one or zero Cong:s. 
    -- If it ends with a cong, we need to distribute it. 
    -- However, it seems hard to come up with a case where the CC algorithm would actually 
    --  introduce a cong in this position. My hunch is that this can never actually happen.
    let (reverse -> end, reverse -> prefix) = takeWhileRight (reverse p')
    case (prefix, end) of
       (_,[]) -> return $ [Left (Assum o (h,p'))]
       (rs, [Cong _ {- the template must be (x y. ATyEq x y) -} [(_,p0),(_,p1)]]) ->
           --wow, this case actually happened!
           trace "Beware, the following code has not been tested." $
              case o of 
                NotSwapped -> 
                 return $ symmChainProof p0 ++ [Left (Assum o (h, rs))] ++ p1
                Swapped -> 
                 return $ symmChainProof p1 ++ [Left (Assum o (h, rs))] ++ p0
       _ -> error "impossible case in fuseProof"
fuseProof (Raw1Refl) = return $ []
fuseProof (Raw1Trans p q) = transProof <$> fuseProof p <*> fuseProof q
fuseProof (Raw1Cong bnd ps) = do
  (xs, template) <- unbind bnd  
  ps' <- fuseProofs xs ps
  return [Right (Cong template ps')]
fuseProof (Raw1Inj i p) = do
  injProof i <$> fuseProof p

fuseProofs :: (Applicative m, Fresh m) => [AName] -> [Raw1Proof] -> m [(AName,ChainProof)]
fuseProofs [] [] = return []
fuseProofs (x:xs) (p:ps) =  do
  p' <- fuseProof p
  ps' <- fuseProofs xs ps
  return $ (x,p'):ps'
fuseProofs [] (_:_) = error "fuseProofs: too few variables (internal error)"
fuseProofs (_:_) [] = error "fuseProofs: too many variables (internal error)"

-- ************ ANNOTATION PHASE
-- Having normalized the proof, in the next phase we annotate it by all the subterms involved.

data AnnotProof = 
    AnnAssum Orientation (ATerm,ATerm,AnnotProof,ATerm,ATerm)
  | AnnRefl ATerm
  | AnnCong ATerm [(AName,ATerm,ATerm,AnnotProof)] ATerm ATerm
  | AnnTrans ATerm ATerm ATerm AnnotProof AnnotProof
  | AnnInj ATerm Int AnnotProof
 deriving Show

-- [synthProof p] takes a SynthProof of A=B and returns A, B and the corresponding AnnotProof
synthProof :: SynthProof -> TcMonad (ATerm,ATerm,AnnotProof)
synthProof (Assum o (n,p)) = do
  (_th ,tyC) <- getType n
  case (tyC, p) of 
    (ATyEq tyA tyB, []) -> case o of
                             NotSwapped -> 
                                 return (tyA, tyB, 
                                         AnnAssum o (n,tyC,AnnRefl tyC,tyA,tyB))
                             Swapped ->
                                 return (tyB, tyA, 
                                         AnnAssum o (n,tyC,AnnRefl tyC,tyA,tyB))
    _  -> do
              (_,ATyEq tyA tyB ,p') <- chainProof (Just tyC) Nothing p
              case o of
                NotSwapped ->
                  return $ (tyA, tyB, AnnAssum o (n,tyC,p',tyA,tyB))
                Swapped ->
                  return $ (tyB, tyA, AnnAssum o (n,tyC,p',tyA,tyB))
synthProof (Inj i p) = do
  (tyA,tyB,p') <- synthProof p
  (l, as) <- runWriterT (decompose False S.empty tyA)
  (_, bs) <- runWriterT (decompose False S.empty tyB)
  return (snd (as !! i), snd (bs !! i), AnnInj l i p')
synthProof (Chain ps) = chainProof Nothing Nothing ps --By precondition to Chain, should work.


-- [checkProof A B p] takes a CheckProof of A=B and returns a corresponding AnnotProof
checkProof :: ATerm -> ATerm -> CheckProof -> TcMonad AnnotProof
checkProof tyA tyB (Cong template ps)  =  do
  subAs <- match (map fst ps) template tyA
  subBs <- match (map fst ps) template tyB
  subpfs <- mapM (\(x,p) -> do 
                              let subA = fromJust $ M.lookup x subAs
                              let subB = fromJust $ M.lookup x subBs
                              (_,_,p') <- chainProof (Just subA) (Just subB) p
                              return (x, subA, subB, p'))
                 ps
  return $ AnnCong template subpfs tyA tyB

-- [chainProof (Just A) (Just B) ps] takes a ChainProof of A=B and returns A, B, and the
-- corresponding AnnotProofs. One can also give Nothing instead of (Just A) if the
-- chain itself has enough information.
chainProof :: (Maybe ATerm) -> (Maybe ATerm) -> ChainProof 
               -> TcMonad (ATerm,ATerm,AnnotProof)
chainProof (Just tyA) _ [] = return $ (tyA, tyA, AnnRefl tyA)
chainProof _ (Just tyB) [] = return $ (tyB, tyB, AnnRefl tyB)

--These two cases (for single-element lists) could be omitted, but give shorter proof terms.
chainProof _ _ [Left p] = synthProof p
chainProof (Just tyA) (Just tyB) [Right p] = (tyA,tyB,) <$> checkProof tyA tyB p

chainProof _ mtyB (Left p : qs) = do 
  (tyA,tyC,p') <- synthProof p
  (_, tyB, qs') <- chainProof (Just tyC) mtyB qs
  return $ (tyA,tyB, AnnTrans tyA tyC tyB p' qs')
chainProof (Just tyA) mtyB (Right p : qs) = do
  (tyC, tyB, qs') <- chainProof Nothing mtyB qs
  p' <- checkProof tyA tyC p
  return $ (tyA, tyB, AnnTrans tyA tyC tyB p' qs')

chainProof Nothing Nothing [] = error "internal error: insufficiently definite ChainProof"
chainProof Nothing _ (Right _ : _) = error "internal error: insufficiently definite ChainProof"


chainProof' :: ATerm -> ATerm -> ChainProof -> TcMonad AnnotProof
chainProof' tyA tyB p = do
  (_,_,p') <- chainProof (Just tyA) (Just tyB) p
  return p'


-- ************* SIMPLIFICATION PHASE
-- We simplify the annotated proof by merging any two adjacent Congs into a single one,
-- and merging Congs and Refls.

simplProof ::  AnnotProof -> AnnotProof
simplProof p@(AnnAssum _ _) = p
simplProof p@(AnnRefl _) = p
simplProof (AnnTrans tyA tyB tyC p q) = AnnTrans tyA tyB tyC (simplProof p) (simplProof q)
simplProof (AnnInj l i p) = AnnInj l i (simplProof p)
simplProof (AnnCong template ps tyA tyB) =  
 let (template', ps') = simplCong (template,[]) ps 
 in (AnnCong template' ps' tyA tyB)
--where 
simplCong :: (ATerm, [(AName,ATerm,ATerm, AnnotProof)])
          -> [(AName,ATerm,ATerm,AnnotProof)] 
          -> (ATerm, [(AName,ATerm,ATerm, AnnotProof)])
simplCong (t, acc) [] = (t, reverse acc)
simplCong (t, acc) ((x,tyA,tyB,_):ps) | tyA `aeq` tyB = 
   simplCong (subst x tyA t, acc) ps
simplCong (t, acc) ((x,tyA,_,AnnRefl _):ps) = 
   simplCong (subst x tyA t, acc) ps
simplCong (t, acc) ((x,tyA,tyB,AnnCong subT subPs _ _):ps) =
   simplCong (subst x subT t, acc) (subPs++ps)
simplCong (t, acc) (p:ps) = simplCong (t, p:acc) ps

-- ************* TERM GENERATION PHASE
-- Final pass: now we can generate the Trellys Core proof terms.

{-
Here is some experimental code to avoid exploding the proof size due to lack of sharing.
But it doesn't seem to work very well, so not using it for now.


--- Here is an utility to help introduce let-bindings for core expressions which are 
-- used more than ones.

data CachedTerm = CachedTerm {
                    cachedName :: AName,      --The name we made for it.
                    cachedVal :: ATerm,
                    cachedUsageCount :: Int,  --The number of times it's been used
                    cachedLevel :: Int        --What order the bindings should be introduced in
                  }

type CacheT key m a = StateT (Map key CachedTerm) m a

cached :: (Fresh m, Ord key) => key -> ATerm -> CacheT key m ATerm
cached k a = do
  cache <- get
  case M.lookup k cache of 
    Nothing ->    do
                    x <- fresh $ string2Name "pf"
                    put (M.insert k (CachedTerm x a 1 (M.size cache)) cache)
                    return $ AVar x
    Just entry -> do
                    put (M.insert k entry{ cachedUsageCount = cachedUsageCount entry + 1 } cache)
                    return $ AVar (cachedName entry)

runCacheT :: CacheT key TcMonad ATerm -> TcMonad ATerm
runCacheT ca = do
  (a, M.elems -> entries) <- runStateT ca M.empty
  let (workhorses, oneoffs) = partition (\e -> cachedUsageCount e > 1) 
                                $ sortBy (compare `on` cachedLevel) entries
  let inlineOneoffs c = foldr (\e b -> subst (cachedName e) (cachedVal e) b) c oneoffs
  inExtendedContext (map (\e -> e{ cachedVal = inlineOneoffs (cachedVal e)}) workhorses)
    $  inlineOneoffs a
 where inExtendedContext [] b = return b
       inExtendedContext (e:es) b = do
          (th,ty) <- getType (cachedVal e)
          y <- fresh $ string2Name "_"
          b' <- extendCtx (ASig (cachedName e) th ty) $ inExtendedContext es b
          return $ ALet Runtime (bind (cachedName e, y, embed (cachedVal e)) b') (th,ty)


genProofTerm' :: AnnotProof -> CacheT (ATerm,ATerm) TcMonad ATerm
genProofTerm' (AnnAssum NotSwapped (Just a,tyA,tyB)) = return $ a
genProofTerm' (AnnAssum Swapped (Just a,tyA,tyB)) = symEq tyA tyB a
genProofTerm' (AnnAssum NotSwapped (Nothing,tyA,tyB)) = return $ AJoin tyA 0 tyB 0 CBV
genProofTerm' (AnnAssum Swapped    (Nothing,tyA,tyB)) = return $ AJoin tyB 0 tyA 0 CBV
genProofTerm' (AnnRefl tyA) =   return (AJoin tyA 0 tyA 0 CBV)
genProofTerm' (AnnCong template ps tyA tyB) = do
  subpfs <- mapM (\(x,subA,subB,p) -> genProofTerm' p)
                 ps                                            
  cached (tyA,tyB) $
         (AConv (AJoin tyA 0 tyA 0 CBV)
                subpfs
                (bind (map (\(x,_,_,_) -> x) ps) (ATyEq tyA template))
                (ATyEq tyA tyB))
genProofTerm' (AnnTrans tyA tyB tyC p q) = do
  p' <- genProofTerm' p
  q' <- genProofTerm' q
  cached (tyA,tyC) =<< transEq tyA tyB tyC p' q'
genProofTerm' (AnnInj l i p) = do
  p' <- genProofTerm' p
  case l of 
    (ATCon _ _) -> return $ ANthEq i p'
    (AAt _ _)   -> return $ AAtEq p'
    _           -> error "internal error: unknown type of injectivity"

genProofTerm :: AnnotProof -> TcMonad ATerm
genProofTerm p = runCacheT (genProofTerm' p)
-}

--genProofTerm :: (Applicative m, Fresh m) => AnnotProof -> m ATerm
genProofTerm :: AnnotProof -> TcMonad ATerm
genProofTerm (AnnAssum NotSwapped (a,_,AnnRefl _,tyA,tyB)) = return $ a 
genProofTerm (AnnAssum NotSwapped (a,tyC,p,tyA,tyB)) = do
  p' <- genProofTerm p
  return $ AConv a p'
genProofTerm (AnnAssum Swapped h@(_,_,_,tyA,tyB)) =
 symEq tyA tyB =<< genProofTerm (AnnAssum NotSwapped h)
genProofTerm (AnnRefl tyA) =   return (AJoin tyA 0 tyA 0 CBV)
genProofTerm (AnnCong template ps tyA tyB) = do
  subpfs <- mapM (\(x,subA,subB,p) -> genProofTerm p)
                 ps
  return $ ACong subpfs
                 (bind (map (\(x,_,_,_) -> x) ps) template)
                 (ATyEq tyA tyB)
genProofTerm (AnnTrans tyA tyB tyC p q) = do
  p' <- genProofTerm p
  q' <- genProofTerm q
  transEq tyA tyB tyC p' q'
genProofTerm (AnnInj l i p) = do
  p' <- genProofTerm p
  case (l,i) of 
    (ATCon _ _,_) -> return $ ANthEq i p'
    (AAt _ _,0)   -> return $ AAtEq p'
    (AArrow _ _ _ _, 0) -> return $ ADomEq p'
    (AArrow _ _ _ _, 1) -> 
      -- It doesn't matter what terms we subtitute in (because of the
      -- way we selected the labels, they will not be in the final equation),
      -- but we need to pick something.
      -- FIXME: the fact that we can just use (Type 0), which does not have the
      -- right type, is a bug in the core type checker...
      return $ ARanEq p' (AType 0) (AType 0)
    _           -> error "internal error: unknown type of injectivity"

-- From (tyA=tyB) and (tyB=tyC), conclude (tyA=tyC).
transEq :: Fresh m => ATerm -> ATerm -> ATerm -> ATerm -> ATerm -> m ATerm
transEq a b c pab pbc = do
  x <- fresh $ string2Name "x"
  return $ AConv pab (ACong [pbc] (bind [x] $ ATyEq a (AVar x)) (ATyEq (ATyEq a b) (ATyEq a c)))  


-- From (tyA=tyB) conclude (tyA=tyB), but in a way that only uses the
-- hypothesis in an erased position.
uneraseEq :: (Fresh m,Applicative m) => ATerm -> ATerm -> ATerm -> m ATerm
uneraseEq tyA tyB p = do
  x <- fresh (string2Name "x")
  -- As an optimization, if the proof term already has no free unerased variables we can just use it as-is.
  pErased <- erase p
  if S.null (fv pErased :: Set EName)
    then return p
    else return $ AConv (AJoin tyA 0 tyA 0 CBV) (ACong [p] (bind [x] (ATyEq tyA (AVar x))) (ATyEq (ATyEq tyA tyA) (ATyEq tyA tyB)))

-- From (tyA=tyB) conlude (tyB=tyA).
symEq :: Fresh m => ATerm -> ATerm -> ATerm -> m ATerm
symEq a b pab = do
  x <- fresh $ string2Name "x"
  return $ AConv (AJoin a 0 a 0 CBV) (ACong [pab] (bind [x] $ ATyEq (AVar x) a) (ATyEq (ATyEq a a) (ATyEq b a)))  

-- From (tyA=tyB), conclude [tyA/x]template = [tyB/x]template
-- For simplicity this function doesn't handle n-ary conv or erased subterms.
congTerm :: (ATerm,ATerm,ATerm) -> AName -> ATerm -> TcMonad ATerm
congTerm (tyA,tyB,pf) x template = do
  y <- fresh $ string2Name "y"  --need a fresh var in case tyB == (AVar hole)
  return (ACong [pf]
                (bind [y] (subst x (AVar y) template))
                (ATyEq (subst x tyA template)
                       (subst x tyB template)))

-- 'decompose False avoid t' returns a new term 's' where each
-- immediate subterm of 't' that does not mention any of the variables
-- in 'avoid' has been replaced by a fresh variable. Furthermore, any
-- erased parts of the term are canonicalized.  The mapping of the
-- introduced fresh variables is recorded in the writer monad.  The
-- boolean argument tracks whether we are looking at a subterm or at
-- the original term.

decompose :: (Monad m, Applicative m, Fresh m) => 
             Bool -> Set AName -> ATerm -> WriterT [(AName,ATerm)] m ATerm
decompose True avoid t | S.null (S.intersection avoid (fv t)) = do
  x <- fresh (string2Name "x")
  tell [(x, t)]
  return $ AVar x
decompose _ avoid t@(AVar _) = return t
decompose _ avoid t@(AUniVar _ _) = return t
decompose isSubterm avoid (ACumul t l) = decompose isSubterm avoid t
decompose _ avoid t@(AType _) = return t
decompose _ avoid (ATCon c args) = do
  args' <- mapM (decompose True avoid) args
  return $ ATCon c args'
decompose _ avoid (ADCon c th params args) = do
  args' <- mapM (\(a,ep) -> case ep of
                              Runtime -> (,Runtime) <$> (decompose True avoid a)
                              Erased  -> return (canonical,Erased))
                args
  return $ ADCon c canonical (map (const canonical) params) args'
decompose _ avoid (AArrow k ex ep bnd) = do
  ((x,unembed->t1), t2) <- unbind bnd
  r1 <- decompose True avoid t1
  r2 <- decompose True (S.insert x avoid) t2
  return (AArrow k ex ep (bind (x, embed r1) r2))
decompose _ avoid (ALam th ty ep bnd) = do
  (x, body) <- unbind bnd 
  r <- decompose True (S.insert x avoid) body
  return (ALam th canonical ep (bind x r))
decompose _ avoid (AApp Runtime t1 t2 ty) = 
  AApp Runtime <$> (decompose True avoid t1) 
               <*> (decompose True avoid t2)
               <*> (pure canonical)
decompose _ avoid (AApp Erased t1 t2 ty) = 
  AApp Erased  <$> (decompose True avoid t1) 
               <*> (pure canonical)
               <*> (pure canonical)
decompose sub avoid (AAt t th) =
  AAt <$> (decompose True avoid t) <*> pure th
decompose isSubterm avoid (AUnbox t) = decompose isSubterm avoid t
decompose isSubterm avoid (ABox t th) = decompose isSubterm avoid t
decompose _ avoid (AAbort t) = return $ AAbort canonical
decompose _ avoid (ATyEq t1 t2) =
  ATyEq <$> (decompose True avoid t1) <*> (decompose True avoid t2)
decompose _ avoid t@(AJoin a i b j strategy) =
  return $ AJoin canonical canonical canonical canonical canonical
decompose isSubterm avoid (AConv t1 pf) =  do
  decompose isSubterm avoid t1
decompose _ avoid (ACong ts bnd ty) =  do
  return $ AJoin canonical canonical canonical canonical canonical  --erases to just "join"
decompose _ avoid (AContra t ty) = 
  return $ AContra canonical canonical
decompose _ avoid (AInjDCon a i) =
  return $ AJoin canonical canonical canonical canonical canonical
decompose _ avoid (ASmaller t1 t2) =
  ASmaller <$> (decompose True avoid t1) <*> (decompose True avoid t2)
decompose _ avoid (AOrdAx t1 t2) =
  return $ AOrdAx canonical canonical
decompose _ avoid (AOrdTrans t1 t2) =
  return $ AOrdAx canonical canonical
decompose _ avoid (AInd ty ep bnd) = do
  ((x,y), t) <- unbind bnd
  r <- decompose True (S.insert x (S.insert y avoid)) t
  return $ AInd canonical ep (bind (x,y) r)  
decompose _ avoid (ARec ty ep bnd) = do
  ((x,y), t) <- unbind bnd
  r <- decompose True (S.insert x (S.insert y avoid)) t
  return $ ARec canonical ep (bind (x,y) r)
decompose _ avoid (ALet Runtime bnd (th,ty)) = do
  ((x,y, unembed->t1), t2) <- unbind bnd
  r1 <- decompose True avoid t1
  r2 <- decompose True (S.insert x (S.insert y avoid)) t2
  return $ ALet Runtime (bind (x,y, embed r1) r2) (th,canonical)
decompose _ avoid (ALet Erased bnd (th,ty)) = do
  ((x,y, unembed->t1), t2) <- unbind bnd
  r2 <- decompose True (S.insert x (S.insert y avoid)) t2
  return $ ALet Erased (bind (x,y, embed canonical) r2) (canonical,canonical)
decompose _ avoid (ACase t1 bnd (th,ty)) = do
  (x, ms) <- unbind bnd
  r1 <- decompose True avoid t1
  rs <- mapM (decomposeMatch (S.insert x avoid)) ms
  return (ACase r1 (bind x rs) (canonical,canonical))
decompose _ avoid (ADomEq a) =
  return $ AJoin canonical canonical canonical canonical canonical
decompose _ avoid (ARanEq p a b) =
  return $ AJoin canonical canonical canonical canonical canonical
decompose _ avoid (AAtEq a) =
  return $ AJoin canonical canonical canonical canonical canonical
decompose _ avoid (ANthEq i a) =
  return $ AJoin canonical canonical canonical canonical canonical
decompose _ avoid (ATrustMe t) = 
  return $ ATrustMe canonical
decompose isSubterm avoid (AHighlight a) = decompose isSubterm avoid a 

decomposeMatch :: (Monad m, Applicative m, Fresh m) => 
                  Set AName -> AMatch -> WriterT [(AName,ATerm)] m AMatch
decomposeMatch avoid (AMatch c bnd) = do
  (args, t) <- unbind bnd
  r <- (decompose True (S.union (binders args) avoid) t)
  return $ AMatch c (bind args r)

-- | match is kind of the opposite of decompose: 
--   [match vars template t] returns the substitution s of terms for the variables in var,
--   such that (erase (substs (toList (match vars template t)) template)) == (erase t)
-- Precondition: t should actually be a substitution instance of template, with those vars.
-- Todo: There is some ambiguity about what exactly the precondition
-- means, since we canonicalize things. So the caller expects
-- (AJoin ...) and (ANthEq ...) to match (and we ensure that they do).
-- Similarly, we make sure that (AConv a ...) and (a)
-- match, and that (ABox a) and (a) match.
match :: (Applicative m, Monad m, Fresh m) => 
         [AName] -> ATerm -> ATerm -> m (Map AName ATerm)
match vars (AVar x) t | x `elem` vars = return $ M.singleton x t
                      | otherwise     = return M.empty
match vars (AUniVar _ _) (AUniVar _ _) = return M.empty
match vars (ACumul t _) (ACumul t' _) = match vars t t'
match vars (AType _) _ = return M.empty
match vars (ATCon c params) (ATCon _ params') = 
  foldr M.union M.empty <$> zipWithM (match vars) params params'
match vars (ADCon c _ _ args) (ADCon _ _ _ args') = do
  foldr M.union M.empty <$> zipWithM (match vars `on` fst) args args'
match vars (AArrow k ex ep bnd) (AArrow k' ex' ep' bnd') = do
  Just ((_,unembed -> t1), t2, (_,unembed -> t1'), t2') <- unbind2 bnd bnd'
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (ALam th ty ep bnd) (ALam th' ty' ep' bnd') = do
  Just (_, t, _, t') <- unbind2 bnd bnd'
  match vars t t'
match vars (AApp Runtime t1 t2 ty) (AApp _ t1' t2' ty') =
  match vars t1 t1' 
   `mUnion` match vars t2 t2'
match vars (AApp Erased t1 t2 ty) (AApp _ t1' t2' ty') =
  match vars t1 t1' 
match vars (AAt t _) (AAt t' _) = match vars t t'
match vars (AUnbox t) t' = match vars t t'
match vars t (AUnbox t') = match vars t t'
match vars (ABox t th) t' = match vars t t'
match vars t (ABox t' th') = match vars t t'
match vars (AAbort t) (AAbort t') = return M.empty
match vars (ATyEq t1 t2) (ATyEq t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars a1 a2 | isJoinVariant a1 && isJoinVariant a2 = return M.empty
match vars t1 (AConv t1' pf') = match vars t1 t1'
match vars (AConv t1 pf) t1' = match vars t1 t1'
match vars (AContra t1 t2) (AContra t1' t2') = return M.empty
match vars (ASmaller t1 t2) (ASmaller t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars a1 a2 | isOrdVariant a1 && isOrdVariant a2 = return M.empty
match vars (AInd ty ep bnd) (AInd ty' ep' bnd') = do
  Just ((_,_), t, (_,_), t') <- unbind2 bnd bnd'
  match vars t t'
match vars (ARec ty ep bnd) (ARec ty' ep' bnd') = do
  Just ((_,_), t, (_,_), t') <- unbind2 bnd bnd'
  match vars t t'
match vars (ALet Runtime bnd (_,ty)) (ALet ep' bnd' (_,ty')) = do
  Just ((_,_,unembed -> t1), t2, (_,_,unembed -> t1'), t2') <- unbind2 bnd bnd'
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (ALet Erased bnd (_,ty)) (ALet ep' bnd' (_,ty')) = do
  Just ((_,_,unembed -> t1), t2, (_,_,unembed -> t1'), t2') <- unbind2 bnd bnd'
  match vars t2 t2'
match vars (ACase t1 bnd (_,ty)) (ACase t1' bnd' (_,ty')) = do
  Just (_, alts, _, alts') <- unbind2 bnd bnd'
  (foldr M.union M.empty <$> zipWithM (matchMatch vars) alts alts')
    `mUnion`  match vars t1 t1'
match vars (ATrustMe t)   (ATrustMe t')    = return M.empty
match vars (AHighlight a) a' = match vars a a'
match vars a (AHighlight a') = match vars a a'
match _ t t' = error $ "internal error: match called on non-matching terms "
                       ++ show t ++ " and " ++ show t' ++ "."

matchMatch :: (Applicative m, Monad m, Fresh m) =>
              [AName] -> AMatch -> AMatch -> m (Map AName ATerm)
matchMatch vars (AMatch _ bnd) (AMatch _ bnd') = do
  Just (_, t, _, t') <- unbind2 bnd bnd'
  match vars t t'

-- Is a some term which erases to just "join"?
isJoinVariant :: ATerm -> Bool
isJoinVariant (AJoin _ _ _ _ _) = True
isJoinVariant (ACong _ _ _) = True
isJoinVariant (AInjDCon _ _) = True
isJoinVariant (ADomEq _) = True
isJoinVariant (ARanEq _ _ _) = True
isJoinVariant (AAtEq _) = True
isJoinVariant (ANthEq _ _) = True
isJoinVariant _ = False

-- Is a some term which erases to just "ord"?
isOrdVariant :: ATerm -> Bool
isOrdVariant (AOrdAx _ _) = True
isOrdVariant (AOrdTrans _ _) = True
isOrdVariant _ = False

-- a short name for (union <$> _ <*> _)
mUnion :: (Applicative m, Ord k) => m (Map k a) -> m (Map k a) -> m (Map k a)
mUnion x y = M.union <$> x <*> y


-- Take a term to think about, and name each subterm in it as a seperate constant,
-- while at the same time propagating equations relating terms to their subterms.
-- Further, we similarly decompose the type of the term, and record the fact that
--  this term inhabits it.
-- Note that erased subterms are not sent on to the congruence closure algorithm.
genEqs :: ATerm -> StateT ProblemState TcMonad Constant
genEqs t = do
  (_,tTy) <- lift $ getType t
  a <- recordName t
  case (eraseToHead t) of 
    AUniVar x _ -> do
                    aTy <- case (eraseToHead tTy) of
                             (AType i) -> recordName tTy
                             _         -> genEqs tTy
                    recordUniVar a x aTy
    _           -> return ()

  (s,ss) <- runWriterT (decompose False S.empty t)
  bs <- mapM genEqs (map (\(x,term) -> term) $ ss)
  let label = (bind (map (\(x,term) -> x) ss) s)

  propagate [(RawRefl,
             Right $ EqBranchConst label bs a)]
  return a

-- Given a binding in the context, name all the intermediate terms in its type.
-- If the type is an equation, we also add the equation itself.
processHyp :: (Theta,ATerm, ATerm) -> StateT ProblemState TcMonad ()
processHyp (th,n,t) = do
  a <- genEqs =<< (lift (zonkTerm n))
  aTy <- genEqs =<< (lift (zonkTerm t))
  recordInhabitant a aTy --If aTy is an equation, this call will propagate it.

-- "Given the context, please prove this other equation."
prove ::  [(Theta,ATerm,ATerm)] -> (ATerm, ATerm) -> TcMonad (Maybe ATerm)
prove hyps (lhs, rhs) = do
  ((c1,c2),st1) <- flip runStateT newState $ do
                     mapM_ processHyp hyps
                     --liftIO $ putStrLn . render . disp $  [DS "prove lhs", DD lhs]
                     c1 <- genEqs =<< (lift (zonkTerm lhs))
                     --liftIO $ putStrLn . render . disp $  [DS "prove rhs", DD rhs]
                     c2 <- genEqs =<< (lift (zonkTerm rhs))
                     return (c1,c2)
  --dumpState st1
  let sts = flip execStateT st1 $
              unify S.empty 
                    [WantedEquation c1 c2]
  case sts of
    [] -> return Nothing
    st:_ -> 
       let bndgs = M.map ((naming st) BM.!>)  (bindings st)
           pf = (proofs st) M.! (WantedEquation c1 c2) in
        do
         {-
         liftIO $ putStrLn $ "Unification successful, calculated bindings " ++ show (M.map (render . disp) bndgs)
         liftIO $ putStrLn $ "Proof is: \n" ++ show pf

         let zonkedAssociated = associateProof $ zonkWithBindings bndgs pf
         liftIO $ putStrLn $ "Associated: \n" ++ show zonkedAssociated

         let symmetrized = symmetrizeProof zonkedAssociated
         liftIO $ putStrLn $ "Symmetrized: \n" ++ show symmetrized

         fused <- fuseProof symmetrized
         liftIO $ putStrLn $ "Fused: \n" ++ show fused

         checked <- chainProof' lhs rhs fused
         liftIO $ putStrLn $ "Checked: \n" ++ show checked

         let simplified = simplProof checked
         liftIO $ putStrLn $ "Simplified: \n" ++ show simplified
         -}

         setUniVars bndgs
         tm <- (genProofTerm 
                  <=< return . simplProof
                  <=< chainProof' lhs rhs
                  <=< fuseProof 
                  . symmetrizeProof 
                  . associateProof 
                  . zonkWithBindings bndgs) pf
         return $ Just tm

-- "Given the context, fill in any remaining evars"
solveConstraints :: [(Theta,ATerm,ATerm)] -> TcMonad ()
solveConstraints hyps = do
   cs   <- getConstraints
   cs'  <- filterM (\(ShouldHaveType x _) -> isNothing <$> lookupUniVar x) cs
   cs'' <- mapM (\(ShouldHaveType x ty) -> ShouldHaveType x <$> zonkTerm ty) cs'
   when (not (null cs'')) $ do
     --liftIO $ putStrLn ("In the context\n" ++
     --                    render (nest 4 (disp hyps)))
     st <- flip execStateT newState $ do
            mapM_ processHyp hyps
            mapM_ (\(ShouldHaveType x ty) -> genEqs (AUniVar x ty))
                  cs''
            guessVars
     let bndgs = M.map ((naming st) BM.!>)  (bindings st)
     oldBndgs <- gets snd
     setUniVars bndgs
     clearConstraints

-------------------------------------------------------

-- A CBV-evaluation context. The name marks the hole, e.g.
--   CbvContext x (AApp (AVar x) (AVar y))
-- represents the context ([] y).
data CbvContext = CbvContext AName ATerm

data ValueFlavour = AnyValue | FunctionValue | ConstructorValue
  deriving (Show,Eq) 

valueFlavour :: ValueFlavour -> ATerm -> Bool
valueFlavour AnyValue = isAnyValue
valueFlavour FunctionValue = isFunctionValue
valueFlavour ConstructorValue = isConstructorValue

isFunctionValue :: ATerm -> Bool
isFunctionValue (eraseToHead -> (ALam _ _ _ _)) = True
isFunctionValue (eraseToHead -> (AInd _ _ _)) = True
isFunctionValue (eraseToHead -> (ARec _ _ _)) = True
isFunctionValue _ = False

isConstructorValue :: ATerm -> Bool
isConstructorValue (eraseToHead -> (ADCon c th params args)) =
  all (isAnyValue . fst) args
isConstructorValue _ = False

-- The use of unsafeUnbind is a bit hacky, but I think it's safe if we only
-- case about the constructor of the term, like here.
isAnyValue :: ATerm -> Bool
isAnyValue (ACumul a lvl) = isAnyValue a
isAnyValue (AType lvl) = True
isAnyValue (ADCon c th params args) = all (isAnyValue . fst) args
isAnyValue (AApp ep a b ty) = False
isAnyValue (ALet Runtime bnd _) = False
isAnyValue (ALet Erased (unsafeUnbind -> ((x,xeq,unembed->a),b)) _) = isAnyValue b
isAnyValue (ACase a bnd _) = False
isAnyValue (ABox a th) = isAnyValue a
isAnyValue (AConv a pf) = isAnyValue a
isAnyValue (ACong _ _ _) = True
isAnyValue (AUniVar x ty) = True
isAnyValue (AVar _) = True
isAnyValue (ATCon _ _) = True
isAnyValue (AArrow _ _ _ _) = True
isAnyValue (ALam _ _ _ _) = True
isAnyValue (AAt _ _) = True
isAnyValue (AUnbox a) = isAnyValue a
isAnyValue (AAbort _) = True
isAnyValue (ATyEq _ _) = True
isAnyValue (AJoin _ _ _ _ _) = True
isAnyValue (AInjDCon _ _) = True
isAnyValue (AContra _ _) = True
isAnyValue (ASmaller _ _) = True
isAnyValue (AOrdAx _ _) = True
isAnyValue (AOrdTrans _ _) = True
isAnyValue (AInd _ _ _) = True
isAnyValue (ARec _ _ _) = True
isAnyValue (ADomEq _) = True
isAnyValue (ARanEq _ _ _) = True
isAnyValue (AAtEq _) = True
isAnyValue (ANthEq _ _) = True
isAnyValue (ATrustMe _) = True
isAnyValue (AHighlight a) = isAnyValue a

{- Split it a term into a CBV evaluation context and a subterm
   which it is "stuck" on.  Also a predicate describing what things can
   be plugged into the hole to let the expression make progress.
   Return None if the term is a value, or if it can already step. -}
aCbvContext :: ATerm -> TcMonad (Maybe (CbvContext, ValueFlavour, ATerm))
aCbvContext (ACumul a lvl) = inCtx (\hole -> ACumul hole lvl) <$> aCbvContext a
-- fixme: think about the dcon case some more. 
--  The problem is that if a dcon is stuck on a single non-value argument, and we use 
--  equational reasoning to replace that arg with a value, then the entire expression
--  is a value, so it still doesn't step, which violates the specification of aCbvContext.
aCbvContext (ADCon c th params args) = return Nothing 
-- aCbvContext (ADCon c th params args) = go [] args
--   where go _ [] = return Nothing
--         go prefix ((a,ep) :args) | isAnyValue a || ep==Erased = go ((a,ep):prefix) args
--                                  | otherwise = do
--            hole <- fresh (string2Name "hole")
--            return $ Just (CbvContext hole (ADCon c th params (reverse prefix ++ [(AVar hole,Runtime)] ++ args)),
--                           AnyValue,
--                           a)
aCbvContext (AApp Erased a b ty) = inCtx (\hole -> AApp Erased hole b ty) <$> aCbvContext a
aCbvContext (AApp Runtime a b ty) | not (isFunctionValue a) = do
  hole <- fresh (string2Name "hole")
  return $ Just (CbvContext hole (AApp Runtime (AVar hole) b ty), FunctionValue, a) 
aCbvContext (AApp Runtime a b ty) | isFunctionValue a && not (isAnyValue b) = do
  hole <- fresh (string2Name "hole")
  return $ Just (CbvContext hole (AApp Runtime a (AVar hole) ty), AnyValue, b)
aCbvContext (AApp Runtime a b ty) | otherwise = return Nothing
aCbvContext (ALet Erased bnd ty) = do
  ((x,xeq,unembed->a), b) <- unbind bnd
  inCtx (\hole -> ALet Erased (bind (x,xeq,embed a) hole) ty) <$> aCbvContext b
aCbvContext (ALet Runtime bnd ty) = do
  ((x,xeq,unembed->a),b) <- unbind bnd
  if (isAnyValue a)
   then return Nothing
   else do
     hole <- fresh (string2Name "hole")
     return $ Just (CbvContext hole (ALet Runtime (bind (x,xeq,embed (AVar hole)) b) ty),
                    AnyValue,
                    a)
aCbvContext (ACase a bnd ty) | not (isConstructorValue a) = do
  hole <- fresh (string2Name "hole")
  return $ Just (CbvContext hole (ACase (AVar hole) bnd ty), ConstructorValue, a)
aCbvContext (ACase a bnd ty) | otherwise = return Nothing
aCbvContext (ABox a th) = inCtx (\hole -> ABox hole th) <$> aCbvContext a
aCbvContext (AConv a pf) = inCtx (\hole -> AConv hole pf) <$> aCbvContext a
-- The rest of the cases are already values:
aCbvContext (ACong _ _ _) = return Nothing
aCbvContext (AUniVar x ty) = return Nothing
aCbvContext (AVar _) = return Nothing
aCbvContext (AType _) = return Nothing
aCbvContext (ATCon _ _) = return Nothing
aCbvContext (AArrow _ _ _ _) = return Nothing
aCbvContext (ALam _ _ _ _) = return Nothing
aCbvContext (AAt _ _) = return Nothing
aCbvContext (AUnbox _) = return Nothing --already a value.
aCbvContext (AAbort _) = return Nothing
aCbvContext (ATyEq _ _) = return Nothing
aCbvContext (AJoin _ _ _ _ _) = return Nothing
aCbvContext (AInjDCon _ _) = return Nothing
aCbvContext (AContra _ _) = return Nothing
aCbvContext (ASmaller _ _) = return Nothing
aCbvContext (AOrdAx _ _) = return Nothing
aCbvContext (AOrdTrans _ _) = return Nothing
aCbvContext (AInd _ _ _) = return Nothing
aCbvContext (ARec _ _ _) = return Nothing
aCbvContext (ADomEq _) = return Nothing
aCbvContext (ARanEq _ _ _) = return Nothing
aCbvContext (AAtEq _) = return Nothing
aCbvContext (ANthEq _ _) = return Nothing
aCbvContext (ATrustMe _) = return Nothing
aCbvContext (AHighlight a) = aCbvContext a

-- Helper function for aCbvContext
inCtx :: (ATerm -> ATerm) -> (Maybe (CbvContext, a, b))
                          -> (Maybe (CbvContext, a, b))
inCtx ctx Nothing = Nothing
inCtx ctx (Just (CbvContext hole ctx', flavour, subterm)) =
           Just (CbvContext hole (ctx ctx'), flavour, subterm)


-- Disp instances, used for debugging.
instance Disp [(Theta, ATerm, ATerm)] where
  disp hyps = 
    vcat $ map (\(th,a,b) ->
                    disp a <+> colon <+> disp b {- <+> text ("(" ++ show b ++")") -})
               hyps

instance Disp EqConstConst where
  disp (EqConstConst a b) = text (show a) <+> text "=" <+> text (show b)

instance Disp (EqBranchConst) where
  disp (EqBranchConst label bs a) = parens (disp label) <+> hsep (map (text . show) bs) <+> text "=" <+> text (show a)

instance Disp (Proof, Equation) where 
  disp (p, eq) = disp p <+> text ":" <+> disp eq

-- In a given context, try to make a step n times, using equational reasoning
-- if it gets stuck.
-- Returns (a', p : a = a') where a' the term that it stepped to.
smartSteps ::  [(Theta,ATerm,ATerm)] -> ATerm -> Int -> TcMonad (ATerm, ATerm)
smartSteps hyps b m = do
  flip evalStateT newState $ do 
    mapM_ processHyp hyps
    steps b m
 where steps :: ATerm -> Int -> StateT ProblemState TcMonad (ATerm,ATerm)
       steps a 0 = do
          --liftIO $ putStrLn.render.disp $ [DS "Out of gas, returning", DD a]
          return $ (a, AJoin a 0 a 0 CBV)
       steps a n = do
          ma' <- smartStep a
          case ma' of
            Nothing -> return $ (a, AJoin a 0 a 0 CBV)
            Just (a', p) -> do
                             --liftIO $ putStrLn.render.disp $ [DS "stepped from", DD a, DS "to", DD a' ]
                             (a'',q) <- steps a' (n-1)
                             pq <- lift $ transEq a a' a'' p q
                             return (a'', pq)


bmlook ::  Bimap ATerm Constant -> ATerm -> Constant
bmlook m x = 
  if BM.member x m
   then m BM.! x
   else error (render (disp x) ++ "is not a member of the map")

-- Given an expression a, find every expression which is CC-equivalent to a and satisfies predi. 
-- Also returns proofs that they are equal. 
-- Uses the union-find structure of the problem state. 
classMembers :: ATerm -> (ATerm -> Bool) -> StateT ProblemState TcMonad [(ATerm, ATerm)]
classMembers a predi = do
  names <- gets naming
  candidates <- classMembersExplain (bmlook names a)
--  candidates <- classMembersExplain (names BM.! a)
  let cs = [(a',p)
            | (c,p) <- candidates,
              let a' = (names BM.!> c),
              predi a']
  mapM (\(a',p) -> do
           -- smartStep and intoArrow will only use one of the list values, 
           -- so ideally we want this to be a lazy thunk (not sure if it is right now).
           pf <- lift $ (genProofTerm 
                         <=< return . simplProof
                         <=< chainProof' a a'
                         <=< fuseProof 
                         . symmetrizeProof 
                         . associateProof) p
           return (a',pf))
       cs


-- Try to step a once, returning Nothing if it is really stuck,
-- or Just (a', pf : a = a').
-- Uses the union-find structure of the problem state.
smartStep :: ATerm -> StateT ProblemState TcMonad (Maybe (ATerm,ATerm))
smartStep a = do
  --liftIO . putStrLn $ "About to step \n" ++ (render . disp $ a) -- ++ "\ni.e.\n" ++ show a
  -- _ <- lift $ aTs a 
  -- liftIO . putStrLn $ "It typechecks, so far"
  _ <- genEqs a
  maybeCtx <- lift $ aCbvContext a
  case maybeCtx of
    Just (CbvContext hole ctx, flavour, b) -> do
       -- liftIO . putStrLn $ "The active subterm is " ++ (render . disp $ b)
       cs <- classMembers b (valueFlavour flavour)
       case cs of 
         (b',pf):_ -> do 
           let a' = subst hole b' ctx
           (do 
               _ <- lift $ getType a'
               cong_pf <- lift $ congTerm (b, b', pf) hole ctx
               -- (liftIO . putStrLn $ "Stepped by existing equality to " ++ (render . disp $ a'))
               return $ Just (a', cong_pf))
             `catchError`
               (\ _ -> do 
                  warn [DS "unfold: the term", DD a, DS "is stuck on the subexpression", DD b,
                        DS "and using an equality proof to change the subterm to", DD b',
                        DS "would create an ill-typed term"]
                  return Nothing)                          
         [] -> lift $ do
                       th <- aGetTh b
                       if (flavour == AnyValue && th == Logic)
                         then Just <$> smartStepLet (CbvContext hole ctx) b
                         else dumbStep a
    Nothing -> lift $ dumbStep a

-- Cleverly introduce an erased binding to allow a term to step when it is stuck 
-- because of the value-restriction for beta-reduction.
--   smartstep ctx b
-- steps the term ctx[b] , which is stuck on the non-value b.
smartStepLet :: CbvContext -> ATerm -> TcMonad (ATerm, ATerm)
smartStepLet (CbvContext hole a) b = do
  -- liftIO . putStrLn $ "About to smartStepLet the term\n" ++ render (nest 2 (disp a))
  --                     ++ "\nby replacing the subterm\n" ++ render (nest 2 (disp b))

  hole_eq <- fresh $ string2Name "hole_eq"
  (Just (a', pf_a_a')) <- dumbStep a  --This should always succeed, or aCbvContext lied to us.
  
  hole_eq_symm <- symEq (AVar hole) b (AVar hole_eq)
  pf_ba_a <- congTerm (b, AVar hole, hole_eq_symm) hole a
  pf_a'_ba' <- congTerm (AVar hole, b, AVar hole_eq) hole a'
  pf_a_ba'  <- transEq a a' (subst hole b a') pf_a_a' pf_a'_ba'
  pf_ba_ba' <- transEq (subst hole b a) a (subst hole b a') pf_ba_a pf_a_ba'

  -- (liftIO . putStrLn $ "Stepped by new equality to " ++ (render . disp $ subst hole b a'))

  return (subst hole b a',
          ALet Erased 
               (bind (hole, hole_eq, embed b) pf_ba_ba')
               (Logic, ATyEq (subst hole b a) (subst hole b a')))

-- Try to step a once, returning Nothing if it is really stuck, or 
-- Just (a', pf : a = a').
-- Uses just the operational semantics, not equational reasoning
dumbStep :: ATerm -> TcMonad (Maybe (ATerm,ATerm))
dumbStep a = do
  --(liftIO . putStrLn $ "Trying to dumb-step " ++ (render . disp $  a))
  ma' <- astep a
  case ma' of
    Nothing -> return Nothing
    Just a' -> do
      --Sometimes astep takes an "extra" step (due to cast-shuffling).
      ea  <- erase a
      ea' <- erase a'
      --(liftIO . putStrLn $ "Dumb step to " ++ (render . disp $  a'))
      if (ea `aeq` ea')
        then return $ Just (a', AJoin a 0 a 0 CBV)
        else return $ Just (a', AJoin a 1 a' 0 CBV)

--See intoArrow for the prototypical use case. 
intoFoo :: (ATerm->Bool) -> ATerm -> ATerm -> StateT ProblemState TcMonad (Maybe (ATerm, ATerm))
-- we can save some work (and get smaller core terms and better error messages)
--  by not changing somthing which already is an arrow/tcon/... type. (Although this does 
--  violate the "respects congruence" property in the paper).
intoFoo isFoo a typ | isFoo typ = return $ Just (a,typ)
intoFoo isFoo a typ = do
  _ <- genEqs typ
  cs <- classMembers typ isFoo
  case cs of
    [] -> return Nothing
    ((typ',pf) : _) -> if typ' `aeq` typ
                         then return $ Just (a, typ)
                         else return $ Just (AConv a pf, typ')

-- Take an arbitrary term 'a' of type 'typ'. Try to find an arrow type 
--  which is equal to 'typ' and apply a coercion to 'a' to make it have that type.
-- Returns the coerced term and its new typ.
-- Uses the union-find structure in the state. 
intoArrow :: ATerm -> ATerm -> StateT ProblemState TcMonad (Maybe (ATerm, ATerm))
intoArrow = intoFoo isArrow

isArrow :: ATerm -> Bool
isArrow (AArrow _ _ _ _) = True
isArrow _ = False

-- like intoArrow, but tries to find a datatype.
intoTCon :: ATerm -> ATerm -> StateT ProblemState TcMonad (Maybe (ATerm, ATerm))
intoTCon = intoFoo isTCon
  where isTCon :: ATerm -> Bool
        isTCon (ATCon _ _) = True
        isTCon _ = False

-- outofFoo isFoo typ ifFoo elseDo
-- uses the union-find structure in the state to find some type typ' which satisfies is foo,
-- then calls (ifDo typ'), and applies a coersion from typ' to typ to waht it rerturned. 
-- If there is no suitable typ', it just returns elseDo, without any coercion.
outofFoo :: (ATerm -> Bool) -> ATerm
            -> (ATerm -> TcMonad ATerm) -> TcMonad ATerm
            -> StateT ProblemState TcMonad ATerm
outofFoo isFoo typ ifDo elseDo = do
  _ <- genEqs typ
  cs <- classMembers typ isFoo
  case cs of
    [] -> lift elseDo
    ((typ',pf) : _) -> 
      if typ' `aeq` typ
        then lift $ ifDo typ
        else do 
              a <- lift $ ifDo typ'
              symPf <- lift $ symEq typ typ' pf 
              return $ AConv a symPf

outofTyEq :: ATerm
            -> (ATerm -> TcMonad ATerm) -> TcMonad ATerm
            -> StateT ProblemState TcMonad ATerm
outofTyEq = outofFoo isTyEq 
  where isTyEq (ATyEq _ _) = True
        isTyEq _ = False

-- For arrows we need to do a bit more work, because we also need to
-- check the injectivity condition.
outofArrow :: ATerm
            -> (ATerm -> TcMonad ATerm) -> TcMonad ATerm
            -> StateT ProblemState TcMonad ATerm
outofArrow typ ifDo elseDo = do
  _ <- genEqs typ
  cs <- classMembers typ isArrow
  case cs of
    [] -> lift elseDo
    ((typ'@(AArrow _  _ _ bnd'),pf) : others) -> do
      --First, check that the injectivity condition holds.
      ((x,unembed->domTy), _) <- unbind bnd'
      extendCtx (ASig x Logic domTy) $ injRngFor typ' (AVar x)

      if typ' `aeq` typ
        then lift $ ifDo typ
        else do 
              a <- lift $ ifDo typ'
              symPf <- lift $ symEq typ typ' pf 
              return $ AConv a symPf


--- Checking the "range injectivity condition"
-- injRngFor hyps ((x:a)->b) c
--  is true if, for every arrow type ((x:a')->b') equal to the arrow,
--  {c/x}b = {c/x}b'.
-- As a precondition, {c/x}b should be well typed.
-- Uses the union-find structure from the state.
injRngFor ::ATerm -> ATerm -> StateT ProblemState TcMonad () 
injRngFor arr@(AArrow _ _ _ bnd) c = do 
  _ <- genEqs arr
  _ <- genEqs c
  ((x, unembed->a), b) <- lift $ unbind bnd
  cs <- classMembers arr isArrow
  forM_ cs $
    (\(arr'@(AArrow _ _ _ bnd'), pf) -> do
        ((x', unembed->a'), b') <- lift $ unbind bnd'
        pf_a <-  symEq a' a (ADomEq pf)  -- pf_c : a = a'
        let ca  = subst x c b
        let ca' = subst x' (AConv c pf_a) b'
        nca   <- genEqs ca
        nca'  <- genEqs ca'
        -- So here is another question: ought we call unify at this point?
        same <- inSameClass nca nca'
        if same
          then return ()
          else err [DS "Injectivity condition failed. Could not prove that", DD ca , DS "and", DD ca', DS "are equal"])
injRngFor _ _ = error "internal error: injRngFor applied to non-arrow expression"
        

-- Build a congruence-closure context, and run a computation in it.
underHypotheses :: [(Theta,ATerm,ATerm)] -> StateT ProblemState TcMonad a -> TcMonad a
underHypotheses hyps a = flip evalStateT newState (do mapM_ processHyp hyps ; a)