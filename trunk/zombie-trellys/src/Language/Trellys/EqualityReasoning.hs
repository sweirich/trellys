{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    GeneralizedNewtypeDeriving,
    UndecidableInstances, OverlappingInstances, TypeSynonymInstances, 
    TupleSections, TypeFamilies #-}

module Language.Trellys.EqualityReasoning (prove) where

import Generics.RepLib hiding (Arrow,Con)
import qualified Generics.RepLib as RL
import Language.Trellys.GenericBind 

import Language.Trellys.Syntax
import Language.Trellys.CongruenceClosure

--import Control.Arrow (second)
import Control.Arrow (second, Kleisli(..), runKleisli)
import Control.Applicative 
import Control.Monad.Writer.Lazy
import Control.Monad.ST
import qualified Data.Set as S
import Data.Set (Set)
import Data.List (intercalate)
import Control.Monad.State.Lazy
import qualified Data.Map as M
import Data.Map (Map)
import Data.Ix
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM

--For testing during development:
import Language.Trellys.Parser
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ as PP

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

type TermLabel = Bind [(Epsilon,TName)] Term

instance Eq TermLabel where
  (==) = aeq
instance Ord TermLabel where
  compare = acompare


-- for testing during development
instance Disp (Epsilon, TName) where
  disp (ep, n) = parens $ disp ep <+> text "," <+> disp n
instance Disp Constant where
  disp = text . show
instance Disp (EqBranchConst TermLabel) where
  disp (EqBranchConst bnd_xs_f ss t) =
    let (xs,f) = unsafeUnbind bnd_xs_f in
      brackets (parens ((hsep (map disp xs)) <+> text "." <+> disp f)  <+> hsep (map disp ss)) <+> text "~=" <+> disp t
instance Show (EqBranchConst TermLabel) where
  show q = render $ disp q

-- A dummy proof type (placeholder during development, to be replaced with something better later):
data DummyProof = DummyProof
  deriving Show

instance Proof DummyProof where
  type Label DummyProof = TermLabel
  refl _    = DummyProof
  symm _    = DummyProof
  trans _ _ = DummyProof
  cong _ _  = DummyProof

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
decompose _ e avoid (Lam eps b) = do
  (x, body) <- unbind b
  r <- decompose True e (S.insert x avoid) body
  return (Lam eps (bind x r))
decompose _ e avoid (App eps t1 t2) = 
  App eps <$> (decompose True e avoid t1) <*> (decompose True (e `orEps` eps) avoid t2)
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


{- Key question is how to handle erased terms. 
   
 -}

-- A monad for naming subterms and recording term-subterm equations.
type DestructureT m a = WriterT [Equation TermLabel] (NamingT Term m) a


-- Take a term to think about, and name each subterm in it as a seperate constant,
-- while at the same time recording equations relating terms to their subterms.
genEqs :: (Monad m, Applicative m, Fresh m) => Term -> DestructureT m Constant
genEqs t = do
  a <- lift $ recordName t
  (s,ss) <- runWriterT (decompose False Runtime S.empty t)
  when (not (null ss)) $ do
    bs <- mapM genEqs (map (\(eps,name,term) -> term) ss)
    (tell [Right $ EqBranchConst (bind (map (\(eps,name,term)->(eps,name)) ss) s)  bs a])
  return a

runDestructureT :: (Monad m) => DestructureT m a -> m ([Equation TermLabel], Bimap Term Constant, a)
runDestructureT x = do
  ((a, eqs), bm) <- flip runNamingT constantSupply $ runWriterT x
  return (eqs, bm, a)
 where constantSupply :: [Constant]
       constantSupply = map Constant [0..]  

-- Given an assumed equation between subterms, name all the intermediate terms, and also add the equation itself.
processHyp :: (Monad m, Applicative m, Fresh m) => (TName, Term, Term) -> DestructureT m ()
processHyp (_,t1,t2) = do
  a1 <- genEqs (delPosParenDeep t1)
  a2 <- genEqs (delPosParenDeep t2)
  tell [Left $ EqConstConst a1 a2]

-- "Given a list of equations, please prove the other equation."
prove :: (Fresh m, Applicative m) => [(TName,Term,Term)] -> (Term, Term) -> m Bool
prove hyps (lhs, rhs) = do
  (eqs, naming , (c1,c2))  <- runDestructureT $ do
                              mapM_ processHyp hyps
                              c1 <- genEqs (delPosParenDeep lhs)
                              c2 <- genEqs (delPosParenDeep rhs)
                              return $ (c1,c2)
  let cmax = maximum (BM.keysR naming)
  return $ runST $ do
    st <- newState (Constant 0, cmax)
    st <- propagate st (map (DummyProof,) eqs)
    rep1 <- find c1 (reprs st)
    rep2 <- find c2 (reprs st)
    return (rep1 == rep2)

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

tryProve :: [String] -> String -> IO Bool
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
  liftIO $ putStrLn ("Input equations are: \n" ++ showEquations eqs)
  liftIO $ putStrLn ("Goal to prove is: \n" ++ showEquation (Left (EqConstConst c1 c2)))
  let (res, endstate) = runST $ do
                                 st <- newState (Constant 0, cmax)
                                 st <- propagate st (map (DummyProof,) eqs)
                                 rep1 <- find c1 (reprs st)
                                 rep2 <- find c2 (reprs st)
                                 endstate <- printState st
                                 return (rep1 == rep2, endstate)
  liftIO $ putStrLn ("\nEnd state is: \n" ++ endstate)
  return res

