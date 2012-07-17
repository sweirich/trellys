{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    GeneralizedNewtypeDeriving, ViewPatterns,
    UndecidableInstances, OverlappingInstances, TypeSynonymInstances, 
    TupleSections, TypeFamilies #-}

module Language.Trellys.EqualityReasoning (prove) where

import Generics.RepLib hiding (Arrow,Con,Refl)
import qualified Generics.RepLib as RL
import Language.Trellys.GenericBind 

import Language.Trellys.Syntax
import Language.Trellys.CongruenceClosure

import Control.Arrow (first, second, Kleisli(..), runKleisli)
import Control.Applicative 
import Control.Monad.Writer.Lazy
import Control.Monad.ST
import Control.Monad.State.Lazy
import Data.Maybe (isJust,fromJust)
import qualified Data.Set as S
import Data.Set (Set)
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Function (on)
import Data.Ix
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM

instance Eq Term where
  (==) = aeq
instance Ord Term where
  compare = acompare

deriving instance Ord Epsilon

-- A convenient monad for recording an association between terms and constants.
newtype NamingT t m a = NamingT (StateT (Bimap t Constant, [Constant]) m a)
  deriving (Monad, MonadTrans, Functor, Applicative)

instance Fresh m => Fresh (NamingT t m) where
  fresh = lift . fresh

recordName :: (Monad m, Ord t) => t -> NamingT t m Constant
recordName t = NamingT $ do
                 (mapping, (c:cs)) <- get
                 case BM.lookup t mapping of
                   Nothing -> do put (BM.insert t c mapping, cs)
                                 return c
                   Just c' -> return c'

runNamingT :: (Monad m) => NamingT t m a -> [Constant] -> m (a, Bimap t Constant)
runNamingT (NamingT m) constantSupply = liftM (second fst) $ runStateT m (BM.empty, constantSupply)

type TermLabel = Bind [(TName,Epsilon)] Term

instance Eq TermLabel where
  (==) = aeq
instance Ord TermLabel where
  compare = acompare

-- This data type just records the operations that the congruence closure algorithm 
-- performs. It is useful to construct this intermediate structure so that we don't have
-- to traverse the proof multiple times when e.g. pushing in Symm
data RawProof =
   RawAssumption (TName, Term, Term)
 | RawRefl
 | RawSymm RawProof
 | RawTrans RawProof RawProof
 | RawCong TermLabel [RawProof]
  deriving Show

instance Proof RawProof where
  type Label RawProof = TermLabel
  refl _ = RawRefl
  symm = RawSymm
  trans = RawTrans 
  cong = RawCong 

-- ********** SYMMETRIZATION PHASE
-- In a first pass we simplify the RawProofs into this datatype, which gets rid of
-- the Symm constructor by pushing it up to the leaves of the tree.

data Orientation = Swapped | NotSwapped
  deriving Show
data Raw1Proof =
   Raw1Assumption Orientation (TName, Term, Term)
 | Raw1Refl
 | Raw1Trans Raw1Proof Raw1Proof
 | Raw1Cong TermLabel [Raw1Proof]
  deriving Show

symmetrizeProof :: RawProof -> Raw1Proof
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
    AssumTrans Orientation (TName,Term,Term) CheckProof
  deriving Show
data CheckProof =
    Synth SynthProof
  | Refl
  | Cong Term [(TName, Maybe CheckProof)]
  | CongTrans Term [(TName, Maybe CheckProof)] SynthProof
 deriving Show

transProof :: CheckProof -> CheckProof -> CheckProof
transProof (Synth (AssumTrans o h p)) q = Synth (AssumTrans o h (transProof p q))
transProof Refl q = q
transProof (Cong l ps) (Synth q) = CongTrans l ps q
transProof (Cong l ps) Refl = Cong l ps
transProof (Cong l ps) (Cong _ qs) = Cong l (zipWith transSubproof ps qs)
transProof (Cong l ps) (CongTrans _ qs r) = CongTrans l (zipWith transSubproof ps qs) r
transProof (CongTrans l ps (AssumTrans o h q)) r =  CongTrans l ps (AssumTrans o h (transProof q r))

transSubproof :: (TName, Maybe CheckProof) -> (TName, Maybe CheckProof) -> (TName, Maybe CheckProof)
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

fuseProofs :: (Applicative m, Fresh m) => [(TName,Epsilon)] -> [Raw1Proof] -> m [(TName,Maybe CheckProof)]
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
    AnnAssum Orientation (TName,Term,Term)
  | AnnRefl Term Term
  | AnnCong Term [(TName,Term,Term,Maybe AnnotProof)]
  | AnnTrans Term Term Term AnnotProof AnnotProof
  
-- [synthProof B p] takes a SynthProof of A=B and returns A and the corresponding AnnotProof
synthProof :: (Applicative m, Fresh m) => Term -> SynthProof -> m (Term,AnnotProof)
synthProof tyB (AssumTrans NotSwapped h@(n,tyA,tyC) p) = do
  q <- checkProof tyC tyB p
  return $ (tyA, AnnTrans tyA tyC tyB (AnnAssum NotSwapped h) q)
synthProof tyB (AssumTrans Swapped    h@(n,tyA,tyC) p) = do
  q <- checkProof tyA tyB p
  return $ (tyC, AnnTrans tyC tyA tyB(AnnAssum Swapped h) q)

-- [checkProof A B p] takes a CongProof of A=B and returns a corresponding AnnotProof
checkProof :: (Applicative m, Fresh m) => Term -> Term -> CheckProof -> m AnnotProof
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
  return $ AnnCong template subpfs
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
            (AnnCong template subpfs)
            tq

-- generate AnnotProof's for a list of equations [ep,tyA,tyB]
checkProofs :: (Applicative m, Fresh m) => [(Epsilon, Term, Term)] -> [CheckProof] -> m [(Term,Term,Maybe AnnotProof)]
checkProofs [] [] = return []
checkProofs ((Runtime,tyA,tyB):goals) (p:ps) = do
  pt <- checkProof tyA tyB p
  ((tyA, tyB, Just pt) :) <$>  (checkProofs goals ps)
checkProofs ((Erased,tyA,tyB):goals) ps =
  ((tyA, tyB, Nothing) :) <$> (checkProofs goals ps)

-- ************* SIMPLIFICATION PHASE
-- We simplify the annotated proof by merging any two adjacent Congs into a single one.

simplProof ::  AnnotProof -> AnnotProof
simplProof p@(AnnAssum _ _) = p
simplProof p@(AnnRefl _ _) = p
simplProof (AnnTrans tyA tyB tyC p q) = AnnTrans tyA tyB tyC (simplProof p) (simplProof q)
simplProof (AnnCong template ps) =  let (template', ps') = simplCong (template,[]) ps 
                                    in (AnnCong template' ps')
  where simplCong (t, acc) [] = (t, reverse acc)
        simplCong (t, acc) ((x,tyA,_,Just (AnnRefl _ _)):ps) = 
           simplCong (subst x tyA t, acc) ps
        simplCong (t, acc) ((x,tyA,tyB,Just (AnnCong subT subPs)):ps) =
           simplCong (subst x subT t, acc) (subPs++ps)
        simplCong (t, acc) (p:ps) = simplCong (t, p:acc) ps


-- ************* TERM GENERATION PHASE
-- Final pass: now we can generate the Trellys Core proof terms.

genProofTerm :: (Applicative m, Fresh m) => AnnotProof -> m Term
genProofTerm (AnnAssum NotSwapped (n,_,_)) = return (Var n)
genProofTerm (AnnAssum Swapped (n,tyA,tyB)) = symmTerm tyA tyB (Var n)
genProofTerm (AnnRefl tyA tyB) =   return (Ann (Join 0 0) (TyEq tyA tyB))
genProofTerm (AnnCong template ps) = do
  let tyA = substs (map (\(x,subA,subB,_) -> (x,subA)) ps) template
  let tyB = substs (map (\(x,subA,subB,_) -> (x,subB)) ps) template
  subpfs <- mapM (\(x,subA,subB,p) -> case p of 
                                      Nothing -> return (TyEq subA subB, Erased)
                                      Just p' -> (,Runtime) <$> genProofTerm p')
                 ps                                            
  return (Conv (Ann (Join 0 0) (TyEq tyA tyA))
               subpfs
               (bind (map (\(x,_,_,_) -> x) ps) (TyEq tyA template)))
genProofTerm (AnnTrans tyA tyB tyC p q) = do
  p' <- genProofTerm p
  q' <- genProofTerm q
  transTerm tyA tyB tyC p' q'

-- From (tyA=tyB) and (tyB=tyC), conclude (tyA=tyC).
transTerm :: Fresh m => Term -> Term -> Term -> Term -> Term -> m Term
transTerm tyA tyB tyC p q = do
  x <- fresh (string2Name "x")
  return $ Conv p [(q,Runtime)] (bind [x] (TyEq tyA (Var x)))

-- From (tyA=tyB) conlude (tyB=tyA).
symmTerm :: Fresh m => Term -> Term -> Term -> m Term
symmTerm tyA tyB p = do
  x <- fresh (string2Name "x")
  return $ Conv (Ann (Join 0 0) (TyEq tyA tyA)) [(p,Runtime)] (bind [x] (TyEq (Var x) tyA))

orEps :: Epsilon -> Epsilon -> Epsilon
orEps Erased _ = Erased
orEps _ Erased = Erased
orEps Runtime Runtime = Runtime

-- 'decompose False avoid t' returns a new term 's' where each immediate
-- subterm of 't' that does not mention any of the variables in 'avoid'
-- has been replaced by a fresh variable. The mapping of the
-- introduced fresh variables is recorded in the writer monad, along with whether
-- the variable occurs in an unerased position or not.
-- The boolean argument tracks whether we are looking at a subterm or at the original term,
-- the epsilon tracks whether we are looking at a subterm in an erased position of the original term.
decompose :: (Monad m, Applicative m, Fresh m) => 
             Bool -> Epsilon -> Set TName -> Term -> WriterT [(Epsilon,TName,Term)] m Term
decompose sub e avoid t | sub && S.null (S.intersection avoid (fv t)) = do
  x <- fresh (string2Name "x")
  tell [(e, x, t)]
  return $ Var x
decompose _ _ avoid t@(Var _) = return t
decompose sub e avoid (Con c args) = do
  args' <- mapM (\(a,ep) -> (,ep) <$> (decompose True (e `orEps` ep) avoid a)) args
  return $ Con c args'
decompose _ _ avoid t@(Type _) = return t
decompose _ e avoid (Lam ep b) = do
  (x, body) <- unbind b
  r <- decompose True e (S.insert x avoid) body
  return (Lam ep (bind x r))
decompose _ e avoid (App ep t1 t2) = 
  App ep <$> (decompose True e avoid t1) <*> (decompose True (e `orEps` ep) avoid t2)
decompose _ e avoid (Let th ep b) = do
  ((x,y, et1), t2) <- unbind b
  let t1 = unembed et1
  r1 <- decompose True (e `orEps` ep) avoid t1
  r2 <- decompose True e (S.insert x (S.insert y avoid)) t2
  return (Let th ep (bind (x,y, embed r1) r2))
decompose _ e avoid (Arrow ep b) = do
  ((x,et1), t2) <- unbind b
  let t1 = unembed et1
  r1 <- decompose True e avoid t1
  r2 <- decompose True e (S.insert x avoid) t2
  return (Arrow ep (bind (x, embed r1) r2))
decompose _ e avoid (Case t1 b) = do
  (x, ms) <- unbind b
  r1 <- decompose True e avoid t1
  rs <- mapM (decomposeMatch e (S.insert x avoid)) ms
  return (Case r1 (bind x rs))
decompose _ e avoid (Smaller t1 t2) =
  liftM2 Smaller (decompose True e avoid t1) (decompose True e avoid t2)
decompose _ e avoid (OrdAx t1) =
  liftM OrdAx (decompose True e avoid t1)
decompose _ e avoid (OrdTrans t1 t2) =
  liftM2 OrdTrans (decompose True e avoid t1) (decompose True e avoid t2)
decompose _ e avoid (TyEq t1 t2) =
  liftM2 TyEq (decompose True e avoid t1) (decompose True e avoid t2)
decompose _ _ avoid t@(Join _ _) = return t
decompose _ e avoid (Conv t1 ts b) =  do
  (xs, t2) <- unbind b
  r1 <- decompose True e avoid t1
  rs <- mapM (runKleisli . first . Kleisli $ decompose True Erased avoid) ts
  r2 <- decompose True Erased (S.union (S.fromList xs) avoid) t2
  return (Conv r1 rs (bind xs r2))
decompose _ e avoid (Contra t) = 
  liftM Contra (decompose True Erased avoid t)
decompose _ e avoid t@Abort = return t
decompose _ e avoid (Rec ep b) = do
  ((x,y), t) <- unbind b
  r <- decompose True e (S.insert x (S.insert y avoid)) t
  return (Rec ep (bind (x,y) r))  
decompose _ e avoid (Ind ep b) = do
  ((x,y), t) <- unbind b
  r <- decompose True e (S.insert x (S.insert y avoid)) t
  return (Ind ep (bind (x,y) r))  
decompose _ e avoid (Ann t1 t2) = 
  liftM2 Ann (decompose True e avoid t1) (decompose True Erased avoid t2)
decompose _ _ _ (Paren _) = error "internal error: decompose called on Paren"
  -- ^^^ Pos/Paren should be deleted in a preprocessing step.
decompose _ _ _ (Pos _ _) = error "internal error: decompose called on Pos" 
  -- ^^^ Pos/Paren should be deleted in a preprocessing step.
decompose sub e avoid (At t th) =
  liftM (\t' -> (At t' th)) (decompose sub e avoid t)
decompose _ _ _ t@TrustMe = return t
decompose _ _ _ InferMe = error "internal error: decompose called on InferMe" 
  -- ^^^ we should only try to infer equations between terms that have already been elaborated.
decompose _ _ _ t = error ("internal error: decompose called on " ++ show t)

decomposeMatch :: (Monad m, Applicative m, Fresh m) => 
                  Epsilon -> Set TName -> Match -> WriterT [(Epsilon,TName,Term)] m Match
decomposeMatch e avoid (Match c cbnd) = do
  (args, t) <- unbind cbnd
  r <- (decompose True e (S.union (S.fromList (map fst args)) avoid) t)
  return $ Match c (bind args r)

-- | match is kind of the opposite of decompose: 
--   [match vars template t] returns the substitution s of terms for the variables in var,
--   such that (substs (toList (match vars template t)) template) == t
-- Precondition: t should actually be a substitution instance of template, with those vars.

match :: (Applicative m, Monad m, Fresh m) => 
         [TName] -> Term -> Term -> m (Map TName Term)
match vars (Var x) t | x `elem` vars = return $ M.singleton x t
                     | otherwise     = return M.empty
match vars (Con c ts) (Con _ ts') = foldr M.union M.empty <$> zipWithM (match vars `on` fst) ts ts'
match vars (Type _) _ = return M.empty
match vars (Lam ep bnd) (Lam ep' bnd') = do
  Just (_, t, _, t') <- unbind2 bnd bnd'
  match vars t t'
match vars (App ep t1 t2) (App ep' t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (Let th ep bnd) (Let th' ep' bnd') = do
  Just ((_,_,unembed -> t1), t2, (_,_,unembed -> t1'), t2') <- unbind2 bnd bnd'
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (Arrow ep bnd) (Arrow ep' bnd') = do
  Just ((_,unembed -> t1), t2, (_,unembed -> t1'), t2') <- unbind2 bnd bnd'
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (Case t1 bnd) (Case t1' bnd') = do
  Just (_, alts, _, alts') <- unbind2 bnd bnd'
  foldr M.union M.empty <$> zipWithM (matchMatch vars) alts alts'
match vars (Smaller t1 t2) (Smaller t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (OrdAx t) (OrdAx t') = match vars t t'
match vars (OrdTrans t1 t2) (OrdTrans t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (TyEq t1 t2) (TyEq t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (Join _ _) (Join _ _) = return M.empty
match vars (Conv t1 t2s bnd) (Conv t1' t2s' bnd') = do
  Just (_, t3, _, t3') <- unbind2 bnd bnd'
  match vars t1 t1'
   `mUnion` (foldr M.union M.empty <$> zipWithM (match vars `on` fst) t2s t2s')
   `mUnion` match vars t3 t3'
match vars (Contra t) (Contra t') = match vars t t'
match vars Abort Abort = return M.empty
match vars (Rec ep bnd) (Rec ep' bnd') = do
  Just ((_,_), t, (_,_), t') <- unbind2 bnd bnd'
  match vars t t'
match vars (Ind ep bnd) (Ind ep' bnd') = do
  Just ((_,_), t, (_,_), t') <- unbind2 bnd bnd'
  match vars t t'
match vars (Ann t1 t2) (Ann t1' t2') =
  match vars t1 t1' `mUnion` match vars t2 t2'
match vars (Paren t) (Paren t') = match vars t t'
match vars (Pos _ t) (Pos _ t') = match vars t t'
match vars (At t _) (At t' _) = match vars t t'
match vars TrustMe TrustMe = return M.empty
match vars InferMe InferMe = return M.empty
match _ t t' = error $ "internal error: match called on non-matching terms "
                       ++ show t ++ " and " ++ show t' ++ "."

matchMatch :: (Applicative m, Monad m, Fresh m) =>
              [TName] -> Match -> Match -> m (Map TName Term)
matchMatch vars (Match _ bnd) (Match _ bnd') = do
  Just (_, t, _, t') <- unbind2 bnd bnd'
  match vars t t'

-- a short name for (union <$> _ <*> _)
mUnion :: (Applicative m, Ord k) => m (Map k a) -> m (Map k a) -> m (Map k a)
mUnion x y = M.union <$> x <*> y

-- A monad for naming subterms and recording term-subterm equations.
type DestructureT m a = WriterT [(RawProof, Equation TermLabel)] (NamingT Term m) a

-- Take a term to think about, and name each subterm in it as a seperate constant,
-- while at the same time recording equations relating terms to their subterms.
-- Note that erased subterms are not sent on to the congruence closure algorithm.
genEqs :: (Monad m, Applicative m, Fresh m) => Term -> DestructureT m Constant
genEqs t = do
  a <- lift $ recordName t
  (s,ss) <- runWriterT (decompose False Runtime S.empty t)
  let ssRuntime = filter (\(ep,name,term) -> ep==Runtime) ss
  when (not (null ssRuntime)) $ do
    bs <- mapM genEqs (map (\(ep,name,term) -> term) $ ssRuntime)
    tell [(RawRefl,
           Right $ EqBranchConst (bind (map (\(ep,name,term)->(name,ep)) ss) s) bs a)]
  return a

runDestructureT :: (Monad m) => DestructureT m a -> m ([(RawProof, Equation TermLabel)], Bimap Term Constant, a)
runDestructureT x = do
  ((a, eqs), bm) <- flip runNamingT constantSupply $ runWriterT x
  return (eqs, bm, a)
 where constantSupply :: [Constant]
       constantSupply = map Constant [0..]  

-- Given an assumed equation between subterms, name all the intermediate terms, and also add the equation itself.
processHyp :: (Monad m, Applicative m, Fresh m) => (TName, Term, Term) -> DestructureT m ()
processHyp h@(_,t1,t2) = do
  a1 <- genEqs (delPosParenDeep t1)
  a2 <- genEqs (delPosParenDeep t2)
  tell [(RawAssumption h, 
         Left $ EqConstConst a1 a2)]

-- "Given a list of equations, please prove the other equation."
prove :: (Fresh m, Applicative m) => [(TName,Term,Term)] -> (Term, Term) -> m (Maybe Term)
prove hyps (lhsPar, rhsPar) = do
  let lhs = delPosParenDeep lhsPar
  let rhs = delPosParenDeep rhsPar
  (eqs, naming , (c1,c2))  <- runDestructureT $ do
                              mapM_ processHyp hyps
                              c1 <- genEqs lhs
                              c2 <- genEqs rhs
                              return $ (c1,c2)
  let cmax = maximum (BM.keysR naming)
  let mpf = runST $ do
             st <- newState (Constant 0, cmax)
             st <- propagate st eqs
             isEqual c1 c2 (reprs st)
  case mpf of
    Nothing -> return Nothing
    Just pf -> Just <$> (genProofTerm <=< return . simplProof <=< checkProof lhs rhs <=< fuseProof . symmetrizeProof) pf 


