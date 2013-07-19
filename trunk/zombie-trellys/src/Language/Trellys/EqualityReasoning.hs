{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    GeneralizedNewtypeDeriving, ViewPatterns,
    UndecidableInstances, OverlappingInstances, TypeSynonymInstances, 
    TupleSections, TypeFamilies #-}

module Language.Trellys.EqualityReasoning 
  (prove, uneraseTerm, smartSteps, zonkTerm, zonkTele) 
where

import Generics.RepLib hiding (Arrow,Con,Refl)
import qualified Generics.RepLib as RL
import Language.Trellys.GenericBind 

import Language.Trellys.TypeMonad
import Language.Trellys.Syntax
import Language.Trellys.Environment(UniVarBindings, setUniVars, warn)
import Language.Trellys.OpSem(erase, eraseToHead)
import Language.Trellys.AOpSem (astep)
import Language.Trellys.TypeCheckCore --(aGetTh, getType)
import Language.Trellys.CongruenceClosure

import Control.Arrow (first, second, Kleisli(..), runKleisli)
import Control.Applicative 
import Control.Monad.Writer.Lazy (WriterT, runWriterT, tell )
import Control.Monad.ST
import Control.Monad.State.Strict
import Control.Monad.Error.Class
import Data.Maybe (isJust,fromJust)
import qualified Data.Set as S
import Data.Set (Set)
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.Function (on)
import Data.Ix

--Stuff used for debugging.
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ ( (<>), (<+>),hsep,text, parens, brackets, nest, render)
import Debug.Trace

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

-- ********** ASSOCIATION PHASE 
-- In a first pass, we associate all uses of trans to the right, which
-- lets us simplify subproofs of the form (trans h (trans (symm h) p))
-- to just p. (This is done by the rawTrans helper function).
-- This is important because such ineffecient proofs are
-- often introduced by the union-find datastructure.

associateProof :: Proof -> Proof
associateProof (RawAssumption h) = RawAssumption h
associateProof RawRefl = RawRefl
associateProof (RawSymm p) = RawSymm (associateProof p)
associateProof (RawTrans p q) = rawTrans (associateProof p) (associateProof q)
associateProof (RawCong l ps) = RawCong l (map associateProof ps)

-- This is a smart constructor for RawTrans
rawTrans :: Proof -> Proof -> Proof
rawTrans RawRefl p = p
rawTrans (RawTrans p q) r = maybeCancel p (rawTrans q r)
  where maybeCancel :: Proof -> Proof -> Proof
        maybeCancel p           (RawTrans (RawSymm q) r) | p==q = r
        maybeCancel (RawSymm p) (RawTrans q r)           | p==q = r
        maybeCancel p q = RawTrans p q
rawTrans p q = RawTrans p q

-- ********** SYMMETRIZATION PHASE
-- Next we simplify the Proofs into this datatype, which gets rid of
-- the Symm constructor by pushing it up to the leaves of the tree.

data Orientation = Swapped | NotSwapped
  deriving (Show,Eq)
data Raw1Proof =
   Raw1Assumption Orientation (Maybe ATerm, ATerm, ATerm)
 | Raw1Refl
 | Raw1Trans Raw1Proof Raw1Proof
 | Raw1Cong Label [Raw1Proof]
  deriving Show

symmetrizeProof :: Proof -> Raw1Proof
symmetrizeProof (RawAssumption h) = Raw1Assumption NotSwapped h
symmetrizeProof (RawSymm (RawAssumption h)) = Raw1Assumption Swapped h
symmetrizeProof RawRefl = Raw1Refl
symmetrizeProof (RawSymm RawRefl) = Raw1Refl
symmetrizeProof (RawSymm (RawSymm p)) = symmetrizeProof p
symmetrizeProof (RawTrans p q) = Raw1Trans (symmetrizeProof p) (symmetrizeProof q)
symmetrizeProof (RawSymm (RawTrans p q)) = Raw1Trans (symmetrizeProof (RawSymm q))
                                                     (symmetrizeProof (RawSymm p))
symmetrizeProof (RawCong l ps) = Raw1Cong l (map symmetrizeProof ps)
symmetrizeProof (RawSymm (RawCong l ps)) = Raw1Cong l (map (symmetrizeProof . RawSymm) ps)

-- ********** NORMALIZATION PHASE
-- The raw1 proof terms are then normalized into this datatype, by
-- associating transitivity to the right and fusing adjacent Congs. 
-- A SynthProof lets you infer the lhs of the equality it is proving,
-- while a CheckProof doesn't.

data SynthProof =
    AssumTrans Orientation (Maybe ATerm,ATerm,ATerm) CheckProof
  deriving Show
data CheckProof =
    Synth SynthProof
  | Refl
  | Cong ATerm [(AName, Maybe CheckProof)]
  | CongTrans ATerm [(AName, Maybe CheckProof)] SynthProof
 deriving Show

transProof :: CheckProof -> CheckProof -> CheckProof
transProof (Synth (AssumTrans o h p)) q = Synth (AssumTrans o h (transProof p q))
transProof Refl q = q
transProof (Cong l ps) (Synth q) = CongTrans l ps q
transProof (Cong l ps) Refl = Cong l ps
transProof (Cong l ps) (Cong _ qs) = Cong l (zipWith transSubproof ps qs)
transProof (Cong l ps) (CongTrans _ qs r) = CongTrans l (zipWith transSubproof ps qs) r
transProof (CongTrans l ps (AssumTrans o h q)) r =  CongTrans l ps (AssumTrans o h (transProof q r))

transSubproof :: (AName, Maybe CheckProof) -> (AName, Maybe CheckProof) -> (AName, Maybe CheckProof)
transSubproof (x,Nothing) (_,Nothing) = (x, Nothing)
transSubproof (x,Just p)  (_,Just q)  = (x, Just $ transProof p q)

fuseProof :: (Applicative m, Fresh m)=> Raw1Proof -> m CheckProof
fuseProof (Raw1Assumption o h) = return $ Synth (AssumTrans o h Refl)
fuseProof (Raw1Refl) = return $ Refl
fuseProof (Raw1Trans Raw1Refl q) = fuseProof q
fuseProof (Raw1Trans (Raw1Assumption o h) q) =  Synth . AssumTrans o h <$> (fuseProof q)
fuseProof (Raw1Trans (Raw1Trans p q) r) = fuseProof (Raw1Trans p (Raw1Trans q r))
fuseProof (Raw1Trans (Raw1Cong bnd ps) q) = do
  (xs, template) <- unbind bnd
  ps' <- fuseProofs xs ps
  q0' <- fuseProof q
  case q0' of
    Synth q'            -> return $ CongTrans template ps' q'
    Refl                -> return $ Cong      template ps'
    (Cong _ qs')        -> return $ Cong      template (zipWith transSubproof ps' qs')
    (CongTrans _ qs' r) -> return $ CongTrans template (zipWith transSubproof ps' qs') r
fuseProof (Raw1Cong bnd ps) = do
  (xs, template) <- unbind bnd  
  Cong template <$> fuseProofs xs ps

fuseProofs :: (Applicative m, Fresh m) => [(AName,Epsilon)] -> [Raw1Proof] -> m [(AName,Maybe CheckProof)]
fuseProofs [] [] = return []
fuseProofs ((x,Runtime):xs) (p:ps) =  do
  p' <- fuseProof p
  ps' <- fuseProofs xs ps
  return $ (x,Just p'):ps'
fuseProofs ((x,Erased):xs) ps =  do
  ps' <- fuseProofs xs ps
  return $ (x, Nothing):ps'

-- ************ ANNOTATION PHASE
-- Having normalized the proof, in the next phase we annotate it by all the subterms involved.

data AnnotProof = 
    AnnAssum Orientation (Maybe ATerm,ATerm,ATerm)
  | AnnRefl ATerm ATerm
  | AnnCong ATerm [(AName,ATerm,ATerm,Maybe AnnotProof)] ATerm ATerm
  | AnnTrans ATerm ATerm ATerm AnnotProof AnnotProof
 deriving Show

-- [synthProof B p] takes a SynthProof of A=B and returns A and the corresponding AnnotProof
synthProof :: (Applicative m, Fresh m) => ATerm -> SynthProof -> m (ATerm,AnnotProof)
synthProof tyB (AssumTrans NotSwapped h@(n,tyA,tyC) p) = do
  q <- checkProof tyC tyB p
  return $ (tyA, AnnTrans tyA tyC tyB (AnnAssum NotSwapped h) q)
synthProof tyB (AssumTrans Swapped    h@(n,tyA,tyC) p) = do
  q <- checkProof tyA tyB p
  return $ (tyC, AnnTrans tyC tyA tyB(AnnAssum Swapped h) q)

-- [checkProof A B p] takes a CheckProof of A=B and returns a corresponding AnnotProof
checkProof :: (Applicative m, Fresh m) => ATerm -> ATerm -> CheckProof -> m AnnotProof
checkProof _ tyB (Synth p) = snd <$> synthProof tyB p
checkProof tyA tyB Refl = return $ AnnRefl tyA tyB
checkProof tyA tyB (Cong template ps)  =  do
  subAs <- match (map (\(x,_)->x) ps) template tyA
  subBs <- match (map (\(x,_)->x) ps) template tyB
  subpfs <- mapM (\(x,mp) -> let subA = fromJust $ M.lookup x subAs
                                 subB = fromJust $ M.lookup x subBs
                             in case mp of 
                                  Nothing -> return (x,subA,subB,Nothing)
                                  Just p -> do
                                              p' <- checkProof subA subB p
                                              return (x, subA, subB, Just p'))
                 ps
  return $ AnnCong template subpfs tyA tyB
checkProof tyA tyC (CongTrans template ps q)  = do
  (tyB, tq) <- synthProof tyC q
  subAs <- match (map (\(x,_)->x) ps) template tyA
  subBs <- match (map (\(x,_)->x) ps) template tyB
  subpfs <- mapM (\(x,mp) -> let subA = fromJust $ M.lookup x subAs
                                 subB = fromJust $ M.lookup x subBs
                             in case mp of 
                                  Nothing -> return (x,subA,subB,Nothing)
                                  Just p -> do
                                              p' <- checkProof subA subB p
                                              return (x, subA, subB, Just p'))
                 ps
  return $ AnnTrans tyA tyB tyC
            (AnnCong template subpfs tyA tyB)
            tq

-- generate AnnotProof's for a list of equations [ep,tyA,tyB]
checkProofs :: (Applicative m, Fresh m) =>
                [(Epsilon, ATerm, ATerm)] -> [CheckProof] -> m [(ATerm,ATerm,Maybe AnnotProof)]
checkProofs [] [] = return []
checkProofs ((Runtime,tyA,tyB):goals) (p:ps) = do
  pt <- checkProof tyA tyB p
  ((tyA, tyB, Just pt) :) <$>  (checkProofs goals ps)
checkProofs ((Erased,tyA,tyB):goals) ps =
  ((tyA, tyB, Nothing) :) <$> (checkProofs goals ps)

-- ************* SIMPLIFICATION PHASE
-- We simplify the annotated proof by merging any two adjacent Congs into a single one,
-- and merging Congs and Refls.

simplProof ::  AnnotProof -> AnnotProof
simplProof p@(AnnAssum _ _) = p
simplProof p@(AnnRefl _ _) = p
simplProof (AnnTrans tyA tyB tyC p q) = AnnTrans tyA tyB tyC (simplProof p) (simplProof q)
simplProof (AnnCong template ps tyA tyB) =  
 let (template', ps') = simplCong (template,[]) ps 
 in (AnnCong template' ps' tyA tyB)
  where simplCong (t, acc) [] = (t, reverse acc)
        simplCong (t, acc) ((x,tyA,tyB,_):ps) | tyA `aeq` tyB = 
           simplCong (subst x tyA t, acc) ps
        simplCong (t, acc) ((x,tyA,_,Just (AnnRefl _ _)):ps) = 
           simplCong (subst x tyA t, acc) ps
        simplCong (t, acc) ((x,tyA,tyB,Just (AnnCong subT subPs _ _)):ps) =
           simplCong (subst x subT t, acc) (subPs++ps)
        simplCong (t, acc) (p:ps) = simplCong (t, p:acc) ps


-- ************* TERM GENERATION PHASE
-- Final pass: now we can generate the Trellys Core proof terms.

genProofTerm :: (Applicative m, Fresh m) => AnnotProof -> m ATerm
genProofTerm (AnnAssum NotSwapped (Just a,tyA,tyB)) = return $ a
genProofTerm (AnnAssum Swapped (Just a,tyA,tyB)) = symmTerm tyA tyB a
genProofTerm (AnnAssum NotSwapped (Nothing,tyA,tyB)) = return $ AJoin tyA 0 tyB 0 CBV
genProofTerm (AnnAssum Swapped    (Nothing,tyA,tyB)) = return $ AJoin tyB 0 tyA 0 CBV
genProofTerm (AnnRefl tyA tyB) =   return (AJoin tyA 0 tyB 0 CBV)
genProofTerm (AnnCong template ps tyA tyB) = do
  -- One might think it should be possible to reconstruct tyA and tyB from 
  -- the template and the subproofs, like so:
  --   let tyA = substs (map (\(x,subA,subB,_) -> (x,subA)) ps) template
  --   let tyB = substs (map (\(x,subA,subB,_) -> (x,subB)) ps) template
  -- But in fact that doesn't work, because we intentionally throw away some information
  -- from the template and replace it with `canonical'. So we need to keep the 
  -- unmutilated template instances around also.
  subpfs <- mapM (\(x,subA,subB,p) -> case p of 
                                      Nothing -> return (ATyEq subA subB, Erased)
                                      Just p' -> (,Runtime) <$> genProofTerm p')
                 ps                                            
  return (AConv (AJoin tyA 0 tyA 0 CBV)
                subpfs
                (bind (map (\(x,_,_,_) -> x) ps) (ATyEq tyA template))
                (ATyEq tyA tyB))
genProofTerm (AnnTrans tyA tyB tyC p q) = do
  p' <- genProofTerm p
  q' <- genProofTerm q
  transTerm tyA tyB tyC p' q'

-- From (tyA=tyB) and (tyB=tyC), conclude (tyA=tyC).
transTerm :: Fresh m => ATerm -> ATerm -> ATerm -> ATerm -> ATerm -> m ATerm
transTerm tyA tyB tyC p q = do
  x <- fresh (string2Name "x")
  return $ AConv p [(q,Runtime)] (bind [x] (ATyEq tyA (AVar x))) (ATyEq tyA tyC)

-- From (tyA=tyB) conclude (tyA=tyB), but in a way that only uses the
-- hypothesis in an erased position.
uneraseTerm :: (Fresh m,Applicative m) => ATerm -> ATerm -> ATerm -> m ATerm
uneraseTerm tyA tyB p = do
  x <- fresh (string2Name "x")
  -- As an optimization, if the proof term already has no free unerased variables we can just use it as-is.
  pErased <- erase p
  if S.null (fv pErased :: Set EName)
    then return p
    else return $ AConv (AJoin tyA 0 tyA 0 CBV) [(p,Runtime)] (bind [x] (ATyEq tyA (AVar x))) (ATyEq tyA tyB)

-- From (tyA=tyB) conlude (tyB=tyA).
symmTerm :: Fresh m => ATerm -> ATerm -> ATerm -> m ATerm
symmTerm tyA tyB p = do
  x <- fresh (string2Name "x")
  return $ AConv (AJoin tyA 0 tyA 0 CBV) [(p,Runtime)] (bind [x] (ATyEq (AVar x) tyA)) (ATyEq tyB tyA)

-- From (tyA=tyB), conclude [tyA/x]template = [tyB/x]template
-- For simplicity this function doesn't handle n-ary conv or erased subterms.
congTerm :: (ATerm,ATerm,ATerm) -> AName -> ATerm -> TcMonad ATerm
congTerm (tyA,tyB,pf) x template = do
  y <- fresh $ string2Name "y"  --need a fresh var in case tyB == (AVar hole)
  return (AConv (AJoin (subst x tyA template) 0 
                       (subst x tyA template) 0
                       CBV)
                [(pf,Runtime)]
                (bind [y] (ATyEq (subst x tyA template) (subst x (AVar y) template)))
                (ATyEq (subst x tyA template)
                       (subst x tyB template)))

----------------------------------------
-- Dealing with unification variables.
----------------------------------------

-- | To zonk a term (this word comes from GHC) means to replace all occurances of 
-- unification variables with their definitions.
zonkTerm :: (Applicative m, MonadState UniVarBindings m) => ATerm -> m ATerm
zonkTerm a = do
  bindings <- get
  return $ zonkWithBindings bindings a

zonkTele :: (Applicative m, MonadState UniVarBindings m) => ATelescope -> m ATelescope
zonkTele tele = do
  bindings <- get
  return $ zonkWithBindings bindings tele

zonkWithBindings :: Rep a => UniVarBindings -> a -> a
zonkWithBindings bindings = RL.everywhere (RL.mkT zonkTermOnce)
  where zonkTermOnce :: ATerm -> ATerm
        zonkTermOnce (AUniVar x ty) = case M.lookup x bindings of
                                        Nothing -> (AUniVar x ty)
                                        Just a -> zonkWithBindings bindings a
        zonkTermOnce a = a


-- 'decompose False avoid t' returns a new term 's' where each immediate
-- subterm of 't' that does not mention any of the variables in 'avoid'
-- has been replaced by a fresh variable. The mapping of the
-- introduced fresh variables is recorded in the writer monad, along with whether
-- the variable occurs in an unerased position or not.
-- The boolean argument tracks whether we are looking at a subterm or at the original term,
-- the epsilon tracks whether we are looking at a subterm in an erased position of the original term.

decompose :: (Monad m, Applicative m, Fresh m) => 
             Bool -> Epsilon -> Set AName -> ATerm -> WriterT [(Epsilon,AName,ATerm)] m ATerm
decompose True e avoid t | S.null (S.intersection avoid (fv t)) = do
  x <- fresh (string2Name "x")
  tell [(e, x, t)]
  return $ AVar x
decompose _ _ avoid t@(AVar _) = return t
decompose _ _ avoid t@(AUniVar _ _) = return t
decompose sub e avoid (ACumul t l) = ACumul <$> (decompose True e avoid t) <*> pure l
decompose _ _ avoid t@(AType _) = return t
decompose sub e avoid (ATCon c args) = do
  args' <- mapM (decompose True e avoid) args
  return $ ATCon c args'
decompose sub e avoid (ADCon c th params args) = do
  params' <- mapM (decompose True Erased avoid) params
  args' <- mapM (\(a,ep) -> (,ep) <$> (decompose True (e `orEps` ep) avoid a)) args
  return $ ADCon c canonical params' args'
decompose _ e avoid (AArrow k ex ep bnd) = do
  ((x,unembed->t1), t2) <- unbind bnd
  r1 <- decompose True e avoid t1
  r2 <- decompose True e (S.insert x avoid) t2
  return (AArrow k ex ep (bind (x, embed r1) r2))
decompose _ e avoid (ALam th ty ep bnd) = do
  (x, body) <- unbind bnd 
  ty' <- decompose True Erased avoid ty
  r <- decompose True e (S.insert x avoid) body
  return (ALam th ty' ep (bind x r))
decompose _ e avoid (AApp ep t1 t2 ty) = 
  AApp ep <$> (decompose True e avoid t1) 
          <*> (decompose True (e `orEps` ep) avoid t2)
          <*> (decompose True Erased avoid ty)
decompose sub e avoid (AAt t th) =
  AAt <$> (decompose True e avoid t) <*> pure th
decompose sub e avoid (AUnbox t) = AUnbox <$> (decompose True e avoid t)
decompose sub e avoid (ABox t th) = ABox <$> (decompose True e avoid t) <*> pure th
decompose _ e avoid (AAbort t) = AAbort <$> (decompose True Erased avoid t)
decompose _ e avoid (ATyEq t1 t2) =
  ATyEq <$> (decompose True e avoid t1) <*> (decompose True e avoid t2)
decompose _ _ avoid t@(AJoin a i b j strategy) =
  AJoin <$> (decompose True Erased avoid a) 
        <*> pure canonical
        <*> (decompose True Erased avoid b) 
        <*> pure canonical
        <*> pure canonical
decompose _ e avoid (AConv t1 ts bnd ty) =  do
  (xs, t2) <- unbind bnd
  r1 <- decompose True e avoid t1
  rs <- mapM (firstM $ decompose True Erased avoid) ts
  r2 <- decompose True Erased (S.union (S.fromList xs) avoid) t2
  ty' <- decompose True Erased avoid ty
  return (AConv r1 rs (bind xs r2) ty')
decompose _ e avoid (AContra t ty) = 
  AContra <$> (decompose True Erased avoid t) <*> (decompose True Erased avoid ty)
decompose _ e avoid (AInjDCon a i) =
  AInjDCon <$> (decompose True e avoid a) <*> pure i
decompose _ e avoid (ASmaller t1 t2) =
  ASmaller <$> (decompose True e avoid t1) <*> (decompose True e avoid t2)
decompose _ e avoid (AOrdAx t1 t2) =
  AOrdAx <$> (decompose True e avoid t1) <*> (decompose True Erased avoid t2)
decompose _ e avoid (AOrdTrans t1 t2) =
  AOrdTrans <$>  (decompose True e avoid t1) <*> (decompose True e avoid t2)
decompose _ e avoid (AInd ty ep bnd) = do
  ((x,y), t) <- unbind bnd
  ty' <- decompose True Erased avoid ty
  r <- decompose True e (S.insert x (S.insert y avoid)) t
  return $ AInd ty' ep (bind (x,y) r)  
decompose _ e avoid (ARec ty ep bnd) = do
  ((x,y), t) <- unbind bnd
  ty' <- decompose True Erased avoid ty
  r <- decompose True e (S.insert x (S.insert y avoid)) t
  return $ ARec ty' ep (bind (x,y) r)
decompose _ e avoid (ALet ep bnd (th,ty)) = do
  ((x,y, unembed->t1), t2) <- unbind bnd
  r1 <- decompose True (e `orEps` ep) avoid t1
  r2 <- decompose True e (S.insert x (S.insert y avoid)) t2
  ty' <- decompose True Erased avoid ty
  return $ ALet ep (bind (x,y, embed r1) r2) (th,ty')
decompose _ e avoid (ACase t1 bnd (th,ty)) = do
  (x, ms) <- unbind bnd
  ty' <- decompose True Erased avoid ty
  r1 <- decompose True e avoid t1
  rs <- mapM (decomposeMatch e (S.insert x avoid)) ms
  return (ACase r1 (bind x rs) (th,ty'))
decompose _ e avoid (ADomEq a) =
  ADomEq <$> decompose True e avoid a
decompose _ e avoid (ARanEq p a b) =
  ARanEq <$> decompose True e avoid p <*> decompose True e avoid a <*> decompose True e avoid b
decompose _ e avoid (AAtEq a) =
  AAtEq <$> (decompose True e avoid a)
decompose _ e avoid (ANthEq i a) =
  ANthEq i <$> decompose True e avoid a
decompose _ _ avoid (ATrustMe t) = 
  ATrustMe <$> (decompose True Erased avoid t)
decompose _ e avoid (ASubstitutedFor t x) =
  ASubstitutedFor <$> (decompose True e avoid t) <*> pure x

decomposeMatch :: (Monad m, Applicative m, Fresh m) => 
                  Epsilon -> Set AName -> AMatch -> WriterT [(Epsilon,AName,ATerm)] m AMatch
decomposeMatch e avoid (AMatch c bnd) = do
  (args, t) <- unbind bnd
  r <- (decompose True e (S.union (binders args) avoid) t)
  return $ AMatch c (bind args r)

-- | match is kind of the opposite of decompose: 
--   [match vars template t] returns the substitution s of terms for the variables in var,
--   such that (substs (toList (match vars template t)) template) == t
-- Precondition: t should actually be a substitution instance of template, with those vars.

match :: (Applicative m, Monad m, Fresh m) => 
         [AName] -> ATerm -> ATerm -> m (Map AName ATerm)
match vars (AVar x) t | x `elem` vars = return $ M.singleton x t
                      | otherwise     = return M.empty
match vars (AUniVar _ _) (AUniVar _ _) = return M.empty
match vars (ACumul t _) (ACumul t' _) = match vars t t'
match vars (AType _) _ = return M.empty
match vars (ATCon c params) (ATCon _ params') = 
  foldr M.union M.empty <$> zipWithM (match vars) params params'
match vars (ADCon c _ params ts) (ADCon _ _ params' ts') = do
   m1 <- foldr M.union M.empty <$> zipWithM (match vars) params params'
   m2 <- foldr M.union M.empty <$> zipWithM (match vars `on` fst) ts ts'
   return (m1 `M.union` m2)
match vars (AArrow k ex ep bnd) (AArrow k' ex' ep' bnd') = do
  Just ((_,unembed -> t1), t2, (_,unembed -> t1'), t2') <- unbind2 bnd bnd'
  match vars t1 t1' `mUnion` match vars t2 t2'
--Fixme: think a bit about ty.
match vars (ALam th ty ep bnd) (ALam th' ty' ep' bnd') = do
  Just (_, t, _, t') <- unbind2 bnd bnd'
  match vars ty ty' `mUnion` match vars t t'
match vars (AApp ep t1 t2 ty) (AApp ep' t1' t2' ty') =
  match vars t1 t1' 
   `mUnion` match vars t2 t2'
   `mUnion` match vars ty ty'
match vars (AAt t _) (AAt t' _) = match vars t t'
match vars (AUnbox t) (AUnbox t') = match vars t t'
match vars (ABox t th) (ABox t' th') = match vars t t'
match vars (AAbort t) (AAbort t') = match vars t t'
match vars (ATyEq t1 t2) (ATyEq t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (AJoin a _ b _ _) (AJoin a' _ b' _ _) = 
  match vars a a' `mUnion` match vars b b'
match vars (AConv t1 t2s bnd ty) (AConv t1' t2s' bnd' ty') = do
  Just (_, t3, _, t3') <- unbind2 bnd bnd'
  match vars t1 t1'
   `mUnion` (foldr M.union M.empty <$> zipWithM (match vars `on` fst) t2s t2s')
   `mUnion` match vars t3 t3'
   `mUnion` match vars ty ty'
match vars (AContra t1 t2) (AContra t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (AInjDCon a i) (AInjDCon a' i') = 
  match vars a a'
match vars (ASmaller t1 t2) (ASmaller t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (AOrdAx t1 t2) (AOrdAx t1' t2') = 
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (AOrdTrans t1 t2) (AOrdTrans t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (AInd ty ep bnd) (AInd ty' ep' bnd') = do
  Just ((_,_), t, (_,_), t') <- unbind2 bnd bnd'
  match vars ty ty' `mUnion` match vars t t'
match vars (ARec ty ep bnd) (ARec ty' ep' bnd') = do
  Just ((_,_), t, (_,_), t') <- unbind2 bnd bnd'
  match vars ty ty' `mUnion` match vars t t'
match vars (ALet ep bnd (_,ty)) (ALet ep' bnd' (_,ty')) = do
  Just ((_,_,unembed -> t1), t2, (_,_,unembed -> t1'), t2') <- unbind2 bnd bnd'
  match vars t1 t1' `mUnion` match vars t2 t2' `mUnion` match vars ty ty'
match vars (ACase t1 bnd (_,ty)) (ACase t1' bnd' (_,ty')) = do
  Just (_, alts, _, alts') <- unbind2 bnd bnd'
  (foldr M.union M.empty <$> zipWithM (matchMatch vars) alts alts')
    `mUnion`  match vars t1 t1'
    `mUnion`  match vars ty ty'
match vars (ADomEq t)     (ADomEq t')      = match vars t t'
match vars (ARanEq p t1 t2) (ARanEq p' t1' t2') = 
     match vars p p' `mUnion` match vars t1 t1' `mUnion` match vars t2 t2'
match vars (AAtEq  t)     (AAtEq  t')      = match vars t t'
match vars (ANthEq _ t)   (ANthEq _ t')    = match vars t t'
match vars (ATrustMe t)   (ATrustMe t')    = match vars t t'
match vars (ASubstitutedFor t _) (ASubstitutedFor t' _) = match vars t t'
match _ t t' = error $ "internal error: match called on non-matching terms "
                       ++ show t ++ " and " ++ show t' ++ "."

matchMatch :: (Applicative m, Monad m, Fresh m) =>
              [AName] -> AMatch -> AMatch -> m (Map AName ATerm)
matchMatch vars (AMatch _ bnd) (AMatch _ bnd') = do
  Just (_, t, _, t') <- unbind2 bnd bnd'
  match vars t t'

-- a short name for (union <$> _ <*> _)
mUnion :: (Applicative m, Ord k) => m (Map k a) -> m (Map k a) -> m (Map k a)
mUnion x y = M.union <$> x <*> y


-- Take a term to think about, and name each subterm in it as a seperate constant,
-- while at the same time propagating equations relating terms to their subterms.
-- Note that erased subterms are not sent on to the congruence closure algorithm.
genEqs :: (Monad m, Applicative m, Fresh m) => ATerm -> StateT ProblemState m Constant
genEqs t = do
  a <- recordName t
  (s,ss) <- runWriterT (decompose False Runtime S.empty t)
  let ssRuntime = filter (\(ep,name,term) -> ep==Runtime) ss
  bs <- mapM genEqs (map (\(ep,name,term) -> term) $ ssRuntime)
  let label = (bind (map (\(ep,name,term)->(name,ep)) ss) s)
  propagate [(RawRefl,
             Right $ EqBranchConst label bs a)]

  when (not (null ssRuntime)) $ do
    --If the head of t is erased, we record an equation saying so.
    sErased <- erase s
    let ((_,x,s1):_) = ssRuntime
    when (sErased `aeq` EVar (translate x)) $
      propagate [(RawAssumption (Nothing, t, s1),
                 Left $ EqConstConst a (head bs))]
  return a

-- Given a binding in the context, name all the intermediate terms in its type.
-- If the type is an equation, we also add the equation itself.
processHyp :: (Monad m, Applicative m, Fresh m) => (Theta,ATerm, ATerm) -> StateT ProblemState m ()
processHyp (_,n,eraseToHead -> ATyEq t1 t2) = do
  a1 <- genEqs t1
  a2 <- genEqs t2
  propagate [(RawAssumption (Just n,t1,t2), 
             Left $ EqConstConst a1 a2)]
processHyp (th,n,t) = genEqs t >> return ()

traceFun :: Bimap ATerm Constant -> String -> WantedEquation -> a -> a
traceFun naming msg (WantedEquation c1 c2) =
        trace (msg ++ " "    ++ (render (parens (disp (naming BM.!> c1))))
                   ++ " == " ++ (render (parens (disp (naming BM.!> c2)))))

noTraceFun :: String -> WantedEquation -> a -> a
noTraceFun msg eq = id

-- "Given the context, please prove this other equation."
prove ::  [(Theta,ATerm,ATerm)] -> (ATerm, ATerm) -> TcMonad (Maybe ATerm)
prove hyps (lhs, rhs) = do
  ((c1,c2),st1) <- flip runStateT newState $ do
                     mapM_ processHyp hyps
                     c1 <- genEqs lhs
                     c2 <- genEqs rhs
                     return (c1,c2)
  let sts = flip execStateT st1 $ do
              unify noTraceFun S.empty [WantedEquation c1 c2]
  case sts of
    [] -> return Nothing
    st:_ -> 
       let bndgs = M.map ((naming st) BM.!>)  (bindings st)
           pf = (proofs st) M.! (WantedEquation (naming st BM.! lhs) 
                                                (naming st BM.! rhs)) in
        do
{-
         let zonkedAssociated = associateProof $ zonkWithBindings bndgs pf
         let symmetrized = symmetrizeProof zonkedAssociated
         fused <- fuseProof symmetrized
         checked <- checkProof lhs rhs fused
         let simplified = simplProof checked

         liftIO $ putStrLn $ "Unification successful, calculated bindings " ++ show (M.map (render . disp) bndgs)
         liftIO $ putStrLn $ "Proof is: \n" ++ show pf
         liftIO $ putStrLn $ "Associated: \n" ++ show zonkedAssociated
         liftIO $ putStrLn $ "Symmetrized: \n" ++ show symmetrized
         liftIO $ putStrLn $ "Fused: \n" ++ show fused
         liftIO $ putStrLn $ "Checked: \n" ++ show checked
         liftIO $ putStrLn $ "Simplified: \n" ++ show simplified
-}
         setUniVars bndgs
         tm <- (genProofTerm 
                  <=< return . simplProof
                  <=< checkProof lhs rhs 
                  <=< fuseProof 
                  . symmetrizeProof 
                  . associateProof 
                  . zonkWithBindings bndgs) pf
         return $ Just tm


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
isAnyValue (ADCon c th params args) = all (isAnyValue . fst) args
isAnyValue (AApp ep a b ty) = False
isAnyValue (ALet Runtime bnd _) = False
isAnyValue (ALet Erased (unsafeUnbind -> ((x,xeq,unembed->a),b)) _) = isAnyValue b
isAnyValue (ACase a bnd _) = False
isAnyValue (ABox a th) = isAnyValue a
isAnyValue (AConv a pfs bnd resTy) = isAnyValue a
isAnyValue (ASubstitutedFor a x) = isAnyValue a
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

{- Split it a term into a CBV evaluation context and a subterm
   which it is "stuck" on.  Also a predicate describing what things can
   be plugged into the hole to let the expression make progress.
   Return None if the term is a value, or if it can already step. -}
aCbvContext :: ATerm -> TcMonad (Maybe (CbvContext, ValueFlavour, ATerm))
aCbvContext (ACumul a lvl) = inCtx (\a -> ACumul a lvl) <$> aCbvContext a
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
aCbvContext (AApp Erased a b ty) = inCtx (\a -> AApp Erased a b ty) <$> aCbvContext a
aCbvContext (AApp Runtime a b ty) | not (isFunctionValue a) = do
  hole <- fresh (string2Name "hole")
  return $ Just (CbvContext hole (AApp Runtime (AVar hole) b ty), FunctionValue, a) 
aCbvContext (AApp Runtime a b ty) | isFunctionValue a && not (isAnyValue b) = do
  hole <- fresh (string2Name "hole")
  return $ Just (CbvContext hole (AApp Runtime a (AVar hole) ty), AnyValue, b)
aCbvContext (AApp Runtime a b ty) | otherwise = return Nothing
aCbvContext (ALet Erased bnd ty) = do
  ((x,xeq,unembed->a), b) <- unbind bnd
  inCtx (\b -> ALet Erased (bind (x,xeq,embed a) b) ty) <$> aCbvContext b
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
aCbvContext (ABox a th) = inCtx (\a -> ABox a th) <$> aCbvContext a
aCbvContext (AConv a pfs bnd resTy) = inCtx (\a -> AConv a pfs bnd resTy) <$> aCbvContext a
aCbvContext (ASubstitutedFor a x) = inCtx (\a -> ASubstitutedFor a x) <$> aCbvContext a
-- The rest of the cases are already values:
aCbvContext (AUniVar x ty) = return Nothing
aCbvContext (AVar _) = return Nothing
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

-- Helper function for aCbvContext
inCtx :: (ATerm -> ATerm) -> (Maybe (CbvContext, a, b))
                          -> (Maybe (CbvContext, a, b))
inCtx ctx Nothing = Nothing
inCtx ctx (Just (CbvContext hole ctx', flavour, subterm)) =
           Just (CbvContext hole (ctx ctx'), flavour, subterm)

---- Some misc. utility functions

firstM :: Monad m => (a -> m b) -> (a,c) -> m (b,c)
firstM = runKleisli . first . Kleisli

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
smartSteps hyps a n = do
  flip evalStateT newState $ do 
    mapM_ processHyp hyps
    steps a n
 where steps :: ATerm -> Int -> StateT ProblemState TcMonad (ATerm,ATerm)
       steps a 0 = return $ (a, AJoin a 0 a 0 CBV)
       steps a n = do
          ma' <- smartStep a
          case ma' of
            Nothing -> return $ (a, AJoin a 0 a 0 CBV)
            Just (a', p) -> do
                             (a'',q) <- steps a' (n-1)
                             pq <- lift $ transTerm a a' a'' p q
                             return (a'', pq)
 
-- Try to step a once, returning Nothing if it is really stuck,
-- or Just (a', pf : a = a').
-- Uses the union-find structor of the problem state.
smartStep :: ATerm -> StateT ProblemState TcMonad (Maybe (ATerm,ATerm))
smartStep a = do
  --liftIO . putStrLn $ "About to step \n" ++ (render . disp $ a) ++ "\ni.e.\n" ++ show a
  _ <- lift $ aTs a 
  --liftIO . putStrLn $ "It typechecks, so far"

  _ <- genEqs a
  maybeCtx <- lift $ aCbvContext a
  case maybeCtx of
    Just (CbvContext hole ctx, flavour, b) -> do
       --liftIO . putStrLn $ "The active subterm is " ++ (render . disp $ b)
       names <- gets naming
       candidates <- classMembersExplain (names BM.! b)
       let cs = [(c,b',p)
                 | (c,p) <- candidates,
                   let b' = (names BM.!> c),
                   valueFlavour flavour b']
       case cs of
         (c,b',p):_ -> do
           pf <- (genProofTerm 
                 <=< return . simplProof
                 <=< checkProof b b'
                 <=< fuseProof 
                 . symmetrizeProof 
                 . associateProof) p
           let a' = subst hole b' ctx
           (do 
               _ <- lift $ aTs a'
               cong_pf <- lift $ congTerm (b, b', pf) hole ctx
               --(liftIO . putStrLn $ "Stepped by existing equality to " ++ (render . disp $ a'))
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
  --liftIO . putStrLn $ "About to smartStepLet the term\n" ++ render (nest 2 (disp a))
  --                     ++ "\nby replacing the subterm\n" ++ render (nest 2 (disp b))

  hole_eq <- fresh $ string2Name "hole_eq"
  (Just (a', pf_a_a')) <- dumbStep a  --This should always succeed, or aCbvContext lied to us.
  
  hole_eq_symm <- symmTerm (AVar hole) b (AVar hole_eq)
  pf_ba_a <- congTerm (b, AVar hole, hole_eq_symm) hole a
  pf_a'_ba' <- congTerm (AVar hole, b, AVar hole_eq) hole a'
  pf_a_ba'  <- transTerm a a' (subst hole b a') pf_a_a' pf_a'_ba'
  pf_ba_ba' <- transTerm (subst hole b a) a (subst hole b a') pf_ba_a pf_a_ba'

  --(liftIO . putStrLn $ "Stepped by new equality to " ++ (render . disp $ subst hole b a'))

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