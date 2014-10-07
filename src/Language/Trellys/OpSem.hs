{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts, TupleSections,
             ViewPatterns  #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | The operational semantics for Trellys core. This module currently has been
-- defined in just-in-time fashion, and should be replaced with an
-- implementation that systematically defines the operational semantics.
module Language.Trellys.OpSem
  (join, cbvStep, cbvNSteps, parStep, isEValue, isValue, erase, eraseToHead)
where

import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint
import Language.Trellys.Environment
import Language.Trellys.TypeMonad
import Language.Trellys.GenericBind

import Control.Applicative 
import Control.Monad hiding (join)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.List (find)

--Stuff used for debugging.
{-
import Language.Trellys.PrettyPrint ()
import Text.PrettyPrint.HughesPJ 
-}

---------------------------------------------------------------
-- Erasing core terms. 
---------------------------------------------------------------
erase :: (Fresh m, Applicative m) => ATerm -> m ETerm
erase (AVar x) = return $ EVar (translate x)
erase (AUniVar x _) = return $ EUniVar (translate x)
erase (ACumul a i) = erase a
erase (AType i) = return $ EType i
erase (ATCon c indxs) = ETCon (translate c) <$> mapM erase indxs
erase (ADCon c _ indxs args) = EDCon (translate c) <$> mapM (erase . fst) (filter ((==Runtime) . snd) args)
erase (AArrow _ ex ep bnd) = do
  ((x, unembed -> a), b) <- unbind bnd
  EArrow ep <$> erase a <*> (bind (translate x) <$> erase b)
erase (ALam _ _ ep bnd) = do
  (x, body) <- unbind bnd
  if ep == Runtime
    then ELam  <$> (bind (translate x) <$> erase body)
    else EILam <$> erase body
erase (AApp Runtime a b ty) = EApp  <$> erase a <*> erase b
erase (AApp Erased a b ty)  = EIApp <$> erase a
erase (AAt a th) = EAt <$> erase a <*> pure th
erase (AUnbox a) = erase a
erase (ABox a th) = erase a
erase (AAbort _) = return EAbort
erase (ATyEq a b) = ETyEq <$> erase a <*> erase b
erase (AJoin a i b j strategy) = return EJoin
erase (AConv a _) = erase a
erase (ACong _ _ _) = return EJoin
erase (AContra a ty) = return EContra
erase (AInjDCon a i) = return EJoin
erase (ASmaller a b) = ESmaller <$> erase a <*> erase b
erase (AOrdAx _ _) = return EOrdAx
erase (AOrdTrans _ _) = return EOrdAx
erase (AInd _ty bnd) = do
  ((f, ys), r) <- unbind bnd
  let eys= map (\(y, ep) -> if ep==Runtime then IsRuntime (translate y) else IsErased)
               ys
  EInd <$> (bind (translate f, eys) <$> erase r)
erase (ARec _ty bnd) = do
  ((f, ys), r) <- unbind bnd
  let eys= map (\(y, ep) -> if ep==Runtime then IsRuntime (translate y) else IsErased)
               ys
  ERec <$> (bind (translate f, eys) <$> erase r)
erase (ALet ep bnd _) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  if ep == Runtime
    then ELet <$> erase a <*> (bind (translate x) <$> erase b)
    else erase b
erase (ACase a bnd _) = do
  (xeq, matchs) <- unbind bnd
  ECase <$> erase a <*> (mapM eraseMatch matchs)
erase (ADomEq _) = return EJoin
erase (ARanEq _ _ _) = return EJoin
erase (AAtEq _) = return EJoin
erase (ANthEq _ _) = return EJoin
erase (ATrustMe _) = return ETrustMe
erase (AHighlight a) = erase a
erase (AReflEq a) = return EJoin
erase (ASymEq a) = return EJoin
erase (ATransEq a b) = return EJoin
erase (AEraseEq a) = return EJoin


eraseMatch  :: (Fresh m, Applicative m) => AMatch -> m EMatch
eraseMatch (AMatch c bnd) = do
  (args, b) <- unbind bnd
  EMatch  (translate c)
      <$> (bind <$> eraseTele args <*> erase b)

eraseTele :: (Fresh m, Applicative m) => ATelescope -> m [EName]
eraseTele AEmpty = return []
eraseTele (ACons (unrebind-> ((x,_,Runtime), tele))) = (translate x:) <$> eraseTele tele
eraseTele (ACons (unrebind-> ((x,_,Erased),  tele))) = eraseTele tele
eraseTele _ = error "Impossible, but GHC can't tell that the above pattern matches are comprehensive."







-- | Remove all completely-erased syntactic form, until we get to the first 
--   constructor which shows up in the erased version.

-- This does the wrong thing for erased lets. 
-- But I really don't want this to live in a monad, and the elaboration algorithm
-- does not introduce erased lets anywhere, so it should not be a problem.
eraseToHead :: ATerm -> ATerm
eraseToHead (ACumul a i) = eraseToHead a
eraseToHead (AUnbox a) = eraseToHead a
eraseToHead (ABox a th) = eraseToHead a
eraseToHead (AConv a _) = eraseToHead a
eraseToHead a = a

-- | Checks if two terms have a common reduct within n full steps
join :: Int -> Int -> ETerm -> ETerm -> EvaluationStrategy -> TcMonad Bool
join s1 s2 m n strategy = do
  let nsteps = case strategy of
                PAR_CBV -> parNSteps
                CBV     -> cbvNSteps
  m' <- nsteps s1 m
  n' <- nsteps s2 n
  let joined = m' `aeq` n'
  unless joined $ do
    warn [DS "Join failure:",
          DD m, DS ("reduces in "++show s1++" steps to"),  DD m',
          DS "and",
          DD n, DS ("reduces in "++show s2++" steps to"),  DD n'
         ]
  return joined

-- | Small-step semantics.
-- Returns Nothing when the argument cannot reduce 
cbvStep :: ETerm -> MaybeT TcMonad ETerm
cbvStep m = cbvStepHead m []

-- This version goes under n-ary function applications. That is,
--   cbvStepHead m [IsRuntime n1, IsErased, IsRuntime n3]
-- is equivalent to
--   cbvStep (EApp (EIApp (EApp m n1)) n2).
cbvStepHead :: ETerm -> [Erasable ETerm] -> MaybeT TcMonad ETerm
cbvStepHead (EVar x) ctx = do 
  d <- MaybeT (lookupDef (translate x))
  ed <- lift (erase d)
  return $ app ed ctx
cbvStepHead a@(EUniVar _)    ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@(ETCon c idxs) ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@(EDCon c args) ctx = stepArgs [] args
  where stepArgs _       []         = app a <$> cbvStepArgs ctx
        stepArgs prefix (v:bs) | isEValue v  = stepArgs (v:prefix) bs
        stepArgs prefix (EAbort:bs) = return EAbort
        stepArgs prefix (b:bs) = do
          b' <- cbvStep b
          return $ app (EDCon c (reverse prefix ++ b' : bs)) ctx
cbvStepHead a@(EType _)        ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@(EArrow _ _ _)   ctx = app a <$> cbvStepArgs ctx
cbvStepHead (ELam bnd)  (IsRuntime v : ctx) | isEValue v = do 
  (x,body) <- unbind bnd
  return $ app (subst x v body) ctx
cbvStepHead a@(ELam _) ctx = app a <$> cbvStepArgs ctx
cbvStepHead (EILam body) (IsErased : ctx) = 
  return $ app body ctx
cbvStepHead (EILam _) _ = mzero
cbvStepHead (EApp a b) ctx = cbvStepHead a (IsRuntime b : ctx)
cbvStepHead (EIApp a) ctx = cbvStepHead a (IsErased : ctx)
cbvStepHead a@(ETyEq _ _)       ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@EJoin             ctx = app a <$> cbvStepArgs ctx
cbvStepHead EAbort              ctx = return EAbort
cbvStepHead a@EContra           ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@(ERec bnd)        ctx | all isEValueArg (take (numArgs bnd) ctx) = do
  ((f,xs), body) <- unbind bnd 
  (usedargs, rest) <- cbvMatchArgs xs ctx
  return $ app (substs usedargs $ subst f a body) rest
cbvStepHead a@(ERec _)          ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@(EInd bnd)        ctx | all isEValueArg (take (numArgs bnd) ctx) = do
  ((f,xs), body) <- unbind bnd
  (usedargs, rest) <- cbvMatchArgs xs ctx
  wa <- lift $ wrapInd xs a
  return $ app (substs usedargs $ subst f wa body) rest
cbvStepHead a@(EInd _)           ctx = app a <$> cbvStepArgs ctx
cbvStepHead (ECase EAbort mtchs) ctx = return EAbort
cbvStepHead (ECase (EDCon c tms) mtchs)   ctx =
  case find (\(EMatch c' _) -> c' == c) mtchs of
     Nothing  -> mzero
     Just (EMatch c' bnd) ->
       do (delta,mtchbody) <- unbind bnd
          guard (length delta == length tms) 
          return $ app (substs (zip delta tms) mtchbody) ctx
cbvStepHead (ECase b mtchs)      ctx = do
  b' <- cbvStep b
  return $ app (ECase b' mtchs) ctx
cbvStepHead a@(ESmaller _ _)     ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@EOrdAx             ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@(EAt _ _)          ctx = app a <$> cbvStepArgs ctx
cbvStepHead a@ETrustMe           ctx = app a <$> cbvStepArgs ctx
cbvStepHead (ELet v bnd)         ctx | isEValue v = do
  (x,n) <- unbind bnd
  return $ app (subst x v n) ctx
cbvStepHead (ELet EAbort bnd)    ctx = return EAbort
cbvStepHead (ELet m bnd)         ctx = do 
  m' <- cbvStep m
  return $ app (ELet m' bnd) ctx

-- In the step rule for Ind, we need to do something like an
-- eta-expansion: instead of substituting 
--   (rec f x1 .. xn . body) 
-- for the recursive variable, we substitute 
--   (\x1 ... xn [] . (rec f x1 .. xn. body) x1 .. xn),
-- in order to get rid of the subterm proof. This
-- function builds that lambda-expression.
wrapInd :: [Erasable EName] -> ETerm -> TcMonad ETerm
wrapInd [] a = return (EILam a)
wrapInd (IsRuntime x : xs) a = do
  x' <- fresh x
  a' <- wrapInd xs (EApp a (EVar x'))
  return $ ELam (bind x' a')
wrapInd (IsErased : xs) a = EILam <$> wrapInd xs (EIApp a)

-- Try to reduce the list of arguments to values.
-- If one of them is a stuck nonvalue, the whole thing is considered stuck.
cbvStepArgs :: [Erasable ETerm] -> MaybeT TcMonad [Erasable ETerm]
cbvStepArgs [] = mzero
cbvStepArgs (IsErased : args) = 
  (IsErased :) <$> cbvStepArgs  args
cbvStepArgs (IsRuntime v:args) | isEValue v = 
  (IsRuntime v :) <$> cbvStepArgs  args
cbvStepArgs (IsRuntime a:args) = 
  (: args) <$> (IsRuntime <$> cbvStep a)

app :: ETerm -> [Erasable ETerm] -> ETerm
app a [] = a
app a (IsRuntime b : bs) = app (EApp a b) bs
app a (IsErased : bs) = app (EIApp a) bs

numArgs :: Bind (EName, [Erasable EName]) ETerm -> Int
numArgs bnd = length xs
  where ((_f,xs),_) = unsafeUnbind bnd

isEValueArg :: Erasable ETerm -> Bool
isEValueArg IsErased = True
isEValueArg (IsRuntime a) = isEValue a

cbvMatchArgs :: [Erasable EName] -> [Erasable ETerm] 
                -> MaybeT TcMonad ([(EName,ETerm)], [Erasable ETerm])
cbvMatchArgs [] as = return ([], as)
cbvMatchArgs (IsErased : xs) (IsErased : as) = cbvMatchArgs xs as
cbvMatchArgs (IsRuntime x:xs) (IsRuntime a:as) = do
  do (usedargs,rest) <- cbvMatchArgs xs as
     return ((x,a) : usedargs, rest)
cbvMatchArgs _ _ = mzero 

-- takes up to n steps
cbvNSteps :: Int -> ETerm -> TcMonad ETerm
cbvNSteps n tm = do
  --liftIO $ putStrLn . render . disp $ [ DS "------->", DD tm ]
  if n == 0 then return tm else
    do stptm <- runMaybeT (cbvStep tm)
       case stptm of
         Nothing -> return tm
         Just tm' -> cbvNSteps (n - 1) tm'

-- | Parallel-reduction small-step semantics.
-- 
-- This reduces zero or more redexes inside a term. 
-- As is standard for parallel reduction relations, it does not try
--  to find further redexes in the subterms of a redex.
--
-- Unlike a standard parallel reduction relation, once it goes under a
-- binder it only reduces lambdas and case-expressions, not ind and rec
-- expressions.  This decreases the risk of unfolding a term
-- indefinitely.  The boolean argument tracks whether we are under a
-- binder, when deep==True we don't unfold ind/rec.
--
parStep :: Bool -> ETerm -> TcMonad ETerm
parStep deep a@(EVar  x)      = do def <- lookupDef (translate x)
                                   case def of 
                                     Nothing -> return a
                                     Just d  -> (erase d)
parStep deep a@(EUniVar _)    = return a
parStep deep (ETCon c idxs)   = ETCon c <$> mapM (parStep deep) idxs
parStep deep (EDCon c args)   = EDCon c <$> mapM (parStep deep) args
parStep deep a@(EType _)      = return a
parStep deep (EArrow ep a bnd) = do
  (x,b) <- unbind bnd
  EArrow ep <$> (parStep True a) <*> (bind x <$> parStep True b)
parStep deep (ELam bnd)       = do
  (x,b) <- unbind bnd
  ELam <$> (bind x <$> parStep True b)
parStep deep (EILam b)         = EILam <$> parStep True b
-- Todo: pstep for n-ary rec/ind.
parStep deep (EApp EAbort _) = return EAbort
parStep deep (EApp _ EAbort) = return EAbort
parStep deep (EApp (ELam bnd) v) | isEValue v = do
  (x,body) <- unbind bnd
  return $ subst x v body
parStep False (EApp a@(ERec bnd) v) | isEValue v = do
  --Todo: fail more gracefully if IsErased
  ((f,[IsRuntime x]),body) <- unbind bnd
  return $ subst f a $ subst x v body
parStep False (EApp a@(EInd bnd) v) | isEValue v = do
  ((f,[IsRuntime x]),body) <- unbind bnd
  x' <- fresh (string2Name "x")
  return $ subst f (ELam (bind x' (EILam (EApp a (EVar x'))))) $ subst x v body
parStep deep (EApp a b) = EApp <$> parStep deep a <*> parStep deep b
parStep deep (EIApp EAbort) = return EAbort
parStep deep (EIApp (EILam body)) = return body
parStep False (EIApp a@(ERec bnd)) = do
  ((f,[IsErased]),body) <- unbind bnd
  return $ subst f a $ body
parStep False (EIApp a@(EInd bnd)) = do
  ((f,[IsErased]),body) <- unbind bnd
  return $ subst f (EILam (EILam (EIApp a))) $ body
parStep deep (EIApp a) = EIApp <$> parStep deep a
--Todo: pstep for n-ary rec/ind
parStep deep (ETyEq a b)     = ETyEq <$> parStep deep a <*> parStep deep b
parStep deep a@EJoin         = return a
parStep deep a@EAbort        = return a 
parStep deep a@EContra       = return a
parStep deep (ERec bnd)  = do
  ((f,args), b) <- unbind bnd
  ERec <$> (bind (f,args) <$> parStep True b)
parStep deep (EInd bnd)  = do
  ((f,args),b) <- unbind bnd
  EInd <$> (bind (f,args) <$> parStep True b)
parStep deep (ECase EAbort _) = return EAbort
parStep deep a@(ECase (EDCon c args) mtchs) | all isEValue args =
  case find (\(EMatch c' _) -> c' == c) mtchs of
    Nothing  -> return a  --This should probably never happen?
    Just (EMatch c' bnd) ->
        do (delta,mtchbody) <- unbind bnd
           if (length delta /= length args) 
             then return a --This should also not happen.
             else return $ substs (zip delta args) mtchbody
parStep deep (ECase a mtchs) = ECase <$> parStep deep a <*> mapM parStepMatch mtchs
  where parStepMatch (EMatch c bnd) = do (xs,b) <- unbind bnd
                                         EMatch c <$> (bind xs <$> parStep True b)
parStep deep (ESmaller a b) = ESmaller <$> parStep deep a <*> parStep deep b
parStep deep a@EOrdAx = return a
parStep deep (ELet EAbort bnd) = return EAbort
parStep deep (ELet v bnd) | isEValue v = do
   (x,b) <- unbind bnd
   return $ subst x v b
parStep deep (ELet a bnd) = do
   (x,b) <- unbind bnd
   a' <- parStep deep a
   b' <- parStep True b
   return $ ELet a' (bind x b')
parStep deep (EAt a th) = EAt <$> parStep deep a <*> pure th
parStep deep a@ETrustMe = return a

-- takes up to n steps
parNSteps :: Int -> ETerm -> TcMonad ETerm
parNSteps 0 a = return a
parNSteps n a = do 
 a' <- parStep False a 
 if (a `aeq` a')
  then return a 
  else parNSteps (n-1) a'

-- | isValue checks to see if a term is a value
-- This is  used in a single place in the entire program, wish I could get rid of it.
isValue :: (Fresh m, Applicative m) => Term -> m Bool
isValue (Var _)            = return True
isValue (TCon _ args)      = return True
isValue (DCon _ args)      = allM (isValue . fst) args
isValue (Type _)           = return True
isValue (Arrow _ _ _)      = return True
isValue (Lam _ _)          = return True
isValue (App _ _ _)        = return False
isValue (Explicitize a)    = isValue a
isValue (Smaller _ _)      = return True
isValue (OrdAx _)          = return True
isValue (OrdTrans _ _)     = return True
isValue (TyEq _ _)         = return True
isValue (Join _ _ _ _)       = return True
isValue Abort              = return False
isValue (Ind _)            = return True
isValue (Rec _)            = return True
isValue (ComplexCase _)    = return False
isValue (Let _ Erased a) = do
  (_,a') <- unbind a 
  isValue a'
isValue (Let _ _ _)        = return False
isValue (Contra _)         = return False
isValue (InjDCon _ _)      = return True
isValue (Ann a _)          = isValue a
isValue (Paren a)          = isValue a
isValue (Pos _ a)          = isValue a
isValue (At _ _)           = return True
isValue (TerminationCase _ _)     = return False
isValue TrustMe            = return True
isValue InferMe            = return False --Hm, dunno.
isValue (Unfold _ _ _ b)     = isValue b  --acts like erased let

-- | checks if an erased term is a value.
isEValue :: ETerm -> Bool
isEValue (EVar _)         = True
isEValue (EUniVar _)      = False
isEValue (ETCon _ _)      = True
isEValue (EDCon _ args)   = all isEValue args
isEValue (EType _)        = True
isEValue (EArrow _ _ _)   = True
isEValue (ELam _)         = True
isEValue (EILam _)        = True
isEValue (EApp _ _)       = False
isEValue (EIApp _)        = False
isEValue (ESmaller _ _)   = True
isEValue EOrdAx           = True
isEValue (ETyEq _ _)      = True
isEValue EJoin            = True
isEValue EAbort           = False
isEValue (ERec _)         = True
isEValue (EInd _)         = True
isEValue (ECase _ _)      = False
isEValue (ELet _ _)       = False
isEValue EContra          = False
isEValue (EAt _ _)        = False
isEValue ETrustMe          = True


