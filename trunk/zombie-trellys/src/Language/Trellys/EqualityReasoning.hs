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

import Control.Arrow (second, Kleisli(..), runKleisli)
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

--For testing during development:
import Language.Trellys.Parser
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ as PP
import Debug.Trace (trace)

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

-- for testing during development
instance Disp (TName,Epsilon) where
  disp (n,ep) = parens $ disp n <+> text "," <+> disp ep
instance Disp Constant where
  disp = text . show
instance Disp (EqBranchConst TermLabel) where
  disp (EqBranchConst bnd_xs_f ss t) =
    let (xs,f) = unsafeUnbind bnd_xs_f in
      brackets (parens ((hsep (map disp xs)) <+> text "." <+> disp f)  <+> hsep (map disp ss)) <+> text "~=" <+> disp t
instance Show (EqBranchConst TermLabel) where
  show q = render $ disp q

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

-- In a first pass we simplify the RawProofs into this datatype, which gets rid of
-- the Symm constructor by pushing it up to the leaves of the tree.

data Orientation = Swapped | NotSwapped
  deriving Show
data Raw1Proof =
   Raw1Assumption Orientation (TName, Term, Term)
 | Raw1Refl
 | Raw1Trans Raw1Proof Raw1Proof
 | Raw1Cong TermLabel [Raw1Proof]

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
  | Cong TermLabel [CheckProof]
  | CongTrans TermLabel [CheckProof] SynthProof
 deriving Show

transProof :: CheckProof -> CheckProof -> CheckProof
transProof (Synth (AssumTrans o h p)) q = Synth (AssumTrans o h (transProof p q))
transProof Refl q = q
transProof (Cong l ps) (Synth q) = CongTrans l ps q
transProof (Cong l ps) Refl = Cong l ps
transProof (Cong l ps) (Cong _ qs) = Cong l (zipWith transProof ps qs)
transProof (Cong l ps) (CongTrans _ qs r) = CongTrans l (zipWith transProof ps qs) r
transProof (CongTrans l ps (AssumTrans o h q)) r =  CongTrans l ps (AssumTrans o h (transProof q r))

fuseProof :: Raw1Proof -> CheckProof
fuseProof (Raw1Assumption o h) = Synth $ AssumTrans o h Refl
fuseProof (Raw1Refl) = Refl
fuseProof (Raw1Trans Raw1Refl q) = fuseProof q
fuseProof (Raw1Trans (Raw1Assumption o h) q) = Synth $ AssumTrans o h (fuseProof q)
fuseProof (Raw1Trans (Raw1Trans p q) r) = fuseProof (Raw1Trans p (Raw1Trans q r))
fuseProof (Raw1Trans (Raw1Cong l ps) q) =
  let ps' = map fuseProof ps in
  case fuseProof q of
    Synth q'            -> CongTrans l ps' q'
    Refl                -> Cong l ps'
    (Cong _ qs')        -> Cong      l (zipWith transProof ps' qs')
    (CongTrans _ qs' r) -> CongTrans l (zipWith transProof ps' qs') r
fuseProof (Raw1Cong l ps) = Cong l (map fuseProof ps)

-- [synthProof B p] takes a SynthProof of A=B and returns A and a Trellys Core proof term of
-- the equality.
synthProof :: (Applicative m, Fresh m) => Term -> SynthProof -> m (Term,Term)
synthProof tyB (AssumTrans NotSwapped (n,tyA,tyC) p) = do
  q1 <- return (Var n)
  q2 <- checkProof tyC tyB p
  (tyA,) <$> transTerm tyA tyC tyB q1 q2
synthProof tyB (AssumTrans Swapped    (n,tyA,tyC) p) = do
  q1 <- symmTerm tyA tyB (Var n)
  q2 <- checkProof tyA tyB p
  (tyC,) <$> transTerm tyC tyA tyB  q1 q2

-- [checkProof A B p] takes a CongProof of A=B and returns a Trellys Core proof term of the
-- equality.
checkProof :: (Applicative m, Fresh m) => Term -> Term -> CheckProof -> m Term
checkProof _ tyB (Synth p) = snd <$> synthProof tyB p
checkProof tyA tyB Refl =
  return (Ann (Join 0 0) (TyEq tyA tyB))
checkProof tyA tyB (Cong bnd ps)  =  do
  (xs, template) <- unbind bnd
  subAs <- match (map fst xs) template tyA
  subBs <- match (map fst xs) template tyB
  subpfs <- zipWith2M (\(x,ep) p -> checkProof (fromJust $ M.lookup x subAs)
                                               (fromJust $ M.lookup x subBs)
                                               p)
                      xs
                      ps
  return (Conv (Ann (Join 0 0) (TyEq tyA tyA))
               (zipWith (\(_,ep) p -> (ep==Erased, p)) xs subpfs)
               (bind (map fst xs) (TyEq tyA template)))
checkProof tyA tyC (CongTrans bnd ps q)  = do
  (tyB, tq) <- synthProof tyC q
  (xs, template) <- unbind bnd
  subAs <- match (map fst xs) template tyA
  subBs <- match (map fst xs) template tyB
  subpfs <- zipWith2M (\(x,ep) p -> checkProof (fromJust $ M.lookup x subAs)
                                               (fromJust $ M.lookup x subBs)
                                               p)
                      xs
                      ps
  transTerm tyA tyB tyC
            (Conv (Ann (Join 0 0) (TyEq tyA tyA))
               (zipWith (\(_,ep) p -> (ep==Erased, p)) xs subpfs)
               (bind (map fst xs) (TyEq tyA template)))
            tq

-- From (tyA=tyB) and (tyB=tyC), conclude (tyA=tyC).
transTerm :: Fresh m => Term -> Term -> Term -> Term -> Term -> m Term
transTerm tyA tyB tyC p q = do
  x <- fresh (string2Name "x")
  return $ Conv p [(False,q)] (bind [x] (TyEq tyA (Var x)))

-- From (tyA=tyB) conlude (tyB=tyA).
symmTerm :: Fresh m => Term -> Term -> Term -> m Term
symmTerm tyA tyB p = do
  x <- fresh (string2Name "x")
  return $ Conv (Ann (Join 0 0) (TyEq tyA tyA)) [(False,p)] (bind [x] (TyEq (Var x) tyA))

orEps :: Epsilon -> Epsilon -> Epsilon
orEps Erased _ = Erased
orEps _ Erased = Erased
orEps Runtime Runtime = Runtime

-- 'decompose False avoid t' returns a new term 's' where each immediate
-- subterm of 't' that does not mention any of the variables in 'avoid'
-- has been replaced by a fresh variable. The mapping of the
-- introduced fresh variables is recorded in the writer monad, along with whether
-- the variable occurs in an unerased position or not.
-- The boolean argument tracks if we are looking at a subterm or at the original term,
-- the epsilon
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
  rs <- mapM (runKleisli . second . Kleisli $ decompose True Erased avoid) ts
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

decomposeMatch :: (Monad m, Applicative m, Fresh m) => 
                  Epsilon -> Set TName -> Match -> WriterT [(Epsilon,TName,Term)] m Match
decomposeMatch e avoid (c,cbnd) = do
  (args, t) <- unbind cbnd
  r <- (decompose True e (S.union (S.fromList (map fst args)) avoid) t)
  return (c, bind args r)

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
   `mUnion` (foldr M.union M.empty <$> zipWithM (match vars `on` snd) t2s t2s')
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
matchMatch vars (_, bnd) (_, bnd') = do
  Just (_, t, _, t') <- unbind2 bnd bnd'
  match vars t t'

-- a short name for (union <$> _ <*> _)
mUnion :: (Applicative m, Ord k) => m (Map k a) -> m (Map k a) -> m (Map k a)
mUnion x y = M.union <$> x <*> y

-- A monad for naming subterms and recording term-subterm equations.
type DestructureT m a = WriterT [(RawProof, Equation TermLabel)] (NamingT Term m) a

-- Take a term to think about, and name each subterm in it as a seperate constant,
-- while at the same time recording equations relating terms to their subterms.
genEqs :: (Monad m, Applicative m, Fresh m) => Term -> DestructureT m Constant
genEqs t = do
  a <- lift $ recordName t
  (s,ss) <- runWriterT (decompose False Runtime S.empty t)
  when (not (null ss)) $ do
    bs <- mapM genEqs (map (\(ep,name,term) -> term) ss)
    tell [(RawRefl,
           Right $ EqBranchConst (bind (map (\(ep,name,term)->(name,ep)) ss) s)  bs a)]
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
    Just pf -> Just <$> (checkProof lhs rhs . fuseProof . symmetrizeProof) pf 

-----------------------------------------------------
-- Some random utility functions

zipWith2M :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWith2M f [] _ = return []
zipWith2M f (x:xs) (y:ys) = liftM (:) (f x y) `ap` (zipWith2M f xs ys)

zipWith3M :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWith3M f [] _ _ = return []
zipWith3M f (x:xs) (y:ys) (z:zs) = liftM (:) (f x y z) `ap` (zipWith3M f xs ys zs)

---------------------------------------------------------------------------------------------
-- The following functions are for experimentation during development.

tryGenEqs str = case parseExpr str of
  Left err -> Left err
  Right t -> Right $ 
    let (eqs, consts, _) = runFreshM $ runDestructureT $ genEqs t
    in
       (eqs, consts)

parseExprOrDie str = 
  case parseExpr str of
  Left err -> error (show err)
  Right t -> t

showNaming :: Bimap Term Constant -> String
showNaming naming = BM.fold showLine "" naming
    where showLine t c rest = show c ++ " := " ++ render (disp t) ++ "\n" ++ rest
    
showEquation :: Equation TermLabel -> String
showEquation (Left (EqConstConst c1 c2)) = show c1 ++ " = " ++ show c2
showEquation (Right (EqBranchConst l cs c)) =  show l ++ " " ++  intercalate " " (map show cs) ++ " = " ++ show c

showEquations = intercalate "\n" . map showEquation

tryProve :: [String] -> String -> IO (Maybe RawProof)
tryProve assmsStr toshowStr = runFreshMT $ do
  let assms = map (\ (Just (t1,t2)) -> (string2Name "_", t1,t2)) $ map (isTyEq . parseExprOrDie) assmsStr
  let Just (lhs,rhs) = isTyEq (parseExprOrDie toshowStr)
  (eqs, naming , (c1,c2))  <- runDestructureT $ do
                              mapM_ processHyp assms
                              c1 <- genEqs lhs
                              c2 <- genEqs  rhs
                              return $ (c1,c2)
  let cmax = maximum (BM.keysR naming)
  liftIO $ putStrLn ("Mapping is: \n" ++ showNaming naming)
  liftIO $ putStrLn ("Input equations are: \n" ++ showEquations (map snd eqs))
  liftIO $ putStrLn ("Goal to prove is: \n" ++ showEquation (Left (EqConstConst c1 c2)))
  let (res, endstate) = runST $ do
                                 st <- newState (Constant 0, cmax)
                                 st <- propagate st  eqs
                                 endstate <- printState st
                                 pf <- isEqual c1 c2 (reprs st)
                                 return (pf, endstate)
  liftIO $ putStrLn ("\nEnd state is: \n" ++ endstate)
  return res


