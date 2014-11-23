
{-# LANGUAGE ViewPatterns, TupleSections, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.AOpSem
  ( isPlainAValue, isConvAValue
  , symEq, transEq
  , astep, asteps
  , aParStep, aParSteps)
where

import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint
import Language.Trellys.Environment 
import Language.Trellys.TypeMonad
import Language.Trellys.GenericBind
import Language.Trellys.TypeCheckCore 
import Language.Trellys.OpSem

import Unbound.LocallyNameless.Types (GenBind)

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Data.List

--Stuff used for debugging.
{-
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ ( (<>), (<+>),hsep,text, parens, brackets, nest, render)

getType a = do
  liftIO $ putStrLn.render.disp $ [ DS "AOpSem calling getType on", DD a ]
  TypeCheckCore.getType a

aTs a = do
  liftIO $ putStrLn.render.disp $ [ DS "AOpSem calling aTs on", DD a ]
  TypeCheckCore.aTs a
-}



isPlainAValue :: (Fresh m, Applicative m) => ATerm -> m Bool
isPlainAValue = fmap isEValue . erase

isConvAValue :: (Fresh m, Applicative m) => ATerm -> m Bool
isConvAValue (AConv a _) = isPlainAValue a
isConvAValue a           = isPlainAValue a

{------------------------------------------------------------------------------}

-- symEq A B (pAB : A = B) : B = A
symEq :: Fresh m => ATerm -> ATerm -> ATerm -> m ATerm
symEq a b pab = return $ ASymEq pab
{-do
  x <- fresh $ string2Name "x"
  return $ AConv (AJoin a 0 a 0 CBV) (ACong [pab] (bind [x] $ ATyEq (AVar x) a) (ATyEq (ATyEq a a) (ATyEq b a)))  
-}

-- transEq A C (pAB : A = B) (pBC : B = C) : A = C
transEq :: Fresh m => ATerm -> ATerm -> ATerm -> ATerm -> ATerm -> m ATerm
transEq a b c pab pbc = return $ ATransEq pab pbc
{- do
  x <- fresh $ string2Name "x"
  return $ AConv pab (ACong [pbc] (bind [x] $ ATyEq a (AVar x)) (ATyEq (ATyEq a b) (ATyEq a c)))  
-}

unbind2M :: (MonadPlus m, Fresh m, Alpha p1, Alpha p2, Alpha t1, Alpha t2)
         => GenBind order card p1 t1
         -> GenBind order card p2 t2
         -> m (p1, t1, p2, t2)
unbind2M bnd bnd' = maybe mzero return =<< unbind2 bnd bnd'


-- For debugging purposes during development, 
-- we wrap aRealParStep in this checking function. 
astep :: ATerm -> TcMonad (Maybe ATerm)
astep a = do
  aE <- erase a
  maE' <- runMaybeT $ cbvStep aE
  ma' <- aRealStep a
  case (maE', ma') of
    (Just aE', Just a') -> do 
       a'E <- erase a'
       unless ((aE' `aeq` a'E) || (a'E `aeq` aE))  $
         warn [DS "Internal error: reduction mismatch for the expression", DD a,
               DS "which erases to", DD aE,
               DS "cbvStep steps to", DD aE',
               DS "astep steps to", DD a',
               DS "which erases to", DD a'E ]
    _ -> return ()
  return ma'


-- If eps == Erased, don't bother stepping.

aRealStep :: ATerm -> TcMonad (Maybe ATerm)
aRealStep (AVar x) = lookupDef x
aRealStep (AUniVar _ _) = return Nothing
aRealStep (ACumul a i) = fmap (flip ACumul i) <$> aRealStep a
aRealStep (AType _) = return Nothing
aRealStep (ATCon _ _) = return Nothing
aRealStep (ADCon c th annots argsOrig) = stepArgs [] argsOrig
  where stepArgs  _     []               = return Nothing
        stepArgs prefix ((arg,eps):args) = do
          stepArg <- aRealStep arg
          case stepArg of
            Nothing         -> stepArgs ((arg,eps):prefix) args
            Just (AAbort t) -> return . Just $ AAbort t
            Just arg'       -> return . Just . ADCon c th annots $
                                 reverse prefix ++ (arg',eps) : args
aRealStep (AArrow _ _ _ _) = return Nothing
aRealStep (ALam _ _ _ _) = return Nothing
{-
aRealStep (AApp eps a b ty) = do
  aval <- isConvAValue a
  if aval
   then do
     stepB <- aRealStep b
     case stepB of
       Just b'         -> return . Just $ AApp eps a b' ty
       Nothing         -> runMaybeT $ stepFun False a b ty 
   else do
     stepA <- aRealStep a
     case stepA of
       Just (AAbort t) -> return . Just $ AAbort t
       Just a'         -> return . Just $ AApp eps a' b ty
       Nothing         -> return Nothing
-}
aRealStep (AApp eps a b ty) = do
  stepA <- aRealStep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ AApp eps a' b ty
    Nothing         -> do
      aval <- isConvAValue a
      if not aval
        then do 
          return Nothing
        else do
          bval <- isConvAValue b
          stepB <- aRealStep b
          case (bval, stepB) of
            (False, Just b') -> return . Just $ AApp eps a b' ty
            _                -> runMaybeT $ stepFun False a b ty 
aRealStep (AAt _ _) = return Nothing
aRealStep (AUnbox a) = do
  stepA <- aRealStep a
  case stepA of
    Just a'         -> return . Just $ AUnbox a'
    Nothing         -> runMaybeT $ stepUnbox a
aRealStep (ABox a th) = fmap (flip ABox th) <$> aRealStep a
aRealStep (AAbort t) = return Nothing
aRealStep (ATyEq _ _) = return Nothing
aRealStep (AJoin _ _ _ _ _) = return Nothing
aRealStep (ACong _ _ _) = return Nothing
aRealStep (AConv a p) = do
  stepA <- aRealStep a
  case stepA of
    Just a'         -> return . Just $ AConv a' p
    Nothing         -> do
      runMaybeT $ stepConv a p
aRealStep (AInjDCon _ _) = return Nothing
aRealStep (AContra _ _) = return Nothing
aRealStep (ASmaller _ _) = return Nothing
aRealStep (AOrdAx _ _) = return Nothing
aRealStep (AOrdTrans _ _) = return Nothing
aRealStep (AInd _ _) = return Nothing
aRealStep (ARec _ _) = return Nothing
aRealStep (ALet eps bnd annot) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  stepA <- aRealStep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ ALet eps (bind (x, xeq, embed a') b) annot
    Nothing         -> do
      aval <- isConvAValue a
      if not aval
        then return Nothing
        else return . Just $ subst x a b
aRealStep (ACase a bnd (th,ty)) = do
  stepA <- aRealStep a
  case stepA of
    Just a'         -> return . Just $ ACase a' bnd (th,ty)
    Nothing         -> runMaybeT $ do
      (eqname, matches) <- unbind bnd
      stepCase a eqname matches ty
aRealStep (ADomEq _) = return Nothing
aRealStep (ARanEq p a a') = return Nothing
aRealStep (AAtEq  _) = return Nothing
aRealStep (ANthEq _ _) = return Nothing
aRealStep (ATrustMe _) = return Nothing
aRealStep (AHighlight a) = aRealStep a
aRealStep (AReflEq _) = return Nothing
aRealStep (ASymEq _) = return Nothing
aRealStep (ATransEq _ _) = return Nothing
aRealStep (AEraseEq _) = return Nothing

-- Beta-reduce an application of a lam, rec, or ind, possibly under a bunch of conversions.
-- The last ATerm is the type of the entire application.
-- The if the Bool is true, only step lambdas, not ind and rec.
stepFun :: Bool -> ATerm -> ATerm -> ATerm -> MaybeT TcMonad ATerm
stepFun onlyLam (eraseToHead -> AAbort _) _  ty = return $ AAbort ty
stepFun onlyLam _ (eraseToHead -> AAbort _)  ty = return $ AAbort ty
-- If a is a converted value we have to do something smart.
stepFun onlyLam (AConv funv p) b ty = do
  --liftIO $ putStrLn . render . disp $ [DS "About to try to step", DD (AConv funv p),
  --                                     DS "applied to", DD b]
  (_, ATyEq (AArrow si srcEx srcEps srcTyBnd)
            (AArrow ri resEx resEps resTyBnd)) <- lift $ getType p
  guardExpected $ si == ri                                           
  guardExpected $ srcEps == resEps
  do -- Scoping
  ( (tyVar, unembed -> srcDom), srcRan,
    (_,     unembed -> resDom), resRan ) <- unbind2M srcTyBnd resTyBnd                        
  let convInput :: ATerm -> ATerm
      convInput v =       AConv v (ADomEq p)  {- :: srcDom -}
  let convOutput :: ATerm {- the input value -}
                    -> ATerm {- the body -}
                    -> ATerm
      convOutput v body = AConv body (ARanEq p (convInput v) v) {- :: (subst tyVar v resRan) -}
  convOutput b <$> stepBareFun onlyLam funv (convInput b)
-- Otherwise, if a is not a converted value, it is either a function value or the 
-- application is stuck, so we let stepBareFun do its thing.
stepFun onlyLam a b ty = stepBareFun onlyLam a b

-- Beta-reduce an application of a lam, rec, or ind.
-- "Bare" means that this function doesn't handle the situation when an AConv blocks the redex.
stepBareFun :: Bool -> ATerm -> ATerm -> MaybeT TcMonad ATerm
stepBareFun onlyLam (ALam _ _ ep bnd) b = do
  when (ep==Runtime) $
    guard =<< (isEValue <$> erase b)
  (x,body) <- unbind bnd
  return  $ subst x b body
stepBareFun False a@(ARec _ty bnd) b = do
  ((f,[(x,ep)]),body) <- unbind bnd   --TODO: n-ary rec
  when (ep==Runtime) $
    guard =<< (isEValue <$> erase b)
  return $ subst f a $ subst x b body
stepBareFun False a@(AInd (eraseToHead -> AArrow i ex epsArr tyBnd) bnd) b = do
  -- We can't use unbind2 here, because bnd and tyBnd have
  -- different numbers of variables.
  --TODO: generalize to n-ary ind.
  ((f,[(x,ep)]),body)           <- unbind bnd   --TODO: n-ary ind
  when (ep==Runtime) $
    guard =<< (isEValue <$> erase b)
  ((tyVar,unembed -> ty1), ty2 ) <- unbind tyBnd
  x'  <- fresh $ string2Name "y"
  p   <- fresh $ string2Name "p"
  let tyArr2 = AArrow i ex       epsArr . bind (x', embed $ ty1)
             $ tyArr1
      tyArr1 = AArrow i Inferred Erased . bind (p,  embed $ ASmaller (AVar x') (AVar x))
             $ (subst tyVar (AVar x') ty2)
      lam    = ALam Logic tyArr2 epsArr   . bind x'
             . ALam Logic tyArr1 Erased   . bind p
             $ AApp epsArr a (AVar x') (subst tyVar (AVar x') ty2)
  return $ subst x b $ subst f lam body
stepBareFun _ _ _ = mzero

-- Beta-reduce an (unbox (box a)) form, possibly with some intervening convs.
-- The ATerm is the expression inside the unbox (excluding the unbox itself).
stepUnbox :: ATerm -> MaybeT TcMonad ATerm
stepUnbox (eraseToHead -> AAbort (AAt ty th)) = return (AAbort ty)
stepUnbox (ABox v _th) = do
  guard =<< (isEValue <$> erase v)
  return v
stepUnbox (AConv (ABox v th) p) = do
  guard =<< (isEValue <$> erase v)
  return (AConv v (AAtEq p))
stepUnbox _ = mzero


-- Beta-reduce (i.e. collapse by transitivity) nested conv expressions.
-- TODO: maybe it would be better to bake this into the other step* functions instead. 
stepConv :: ATerm -> ATerm -> MaybeT TcMonad ATerm
stepConv (AAbort ty) p = do
  (_, ATyEq _ty1 ty2) <- lift $ getType p
  return $ AAbort ty2
stepConv (AConv v q) p = do
  guard =<< (isEValue <$> erase v)
  (_, ATyEq ty1 ty2) <- lift $ getType q
  (_, ATyEq ty2' ty3) <- lift $ getType p
  pq <- (transEq ty1 ty2 ty3 q p)
  return  $ AConv v pq
stepConv _ _ = mzero

-- Beta-reduce a case expression (the arguments are scrutinee, equation name, branches, type of the entire case-expression)
stepCase :: ATerm -> AName -> [AMatch] -> ATerm -> MaybeT TcMonad ATerm
stepCase (AConv (ADCon c th indices vs) b) eqname matches ty = do
          (_, ATyEq (eraseToHead -> ATCon srcTCon srcIndices)
                    (eraseToHead -> ATCon resTCon resIndices)) <- lift $ getType b
          guardExpected $ srcTCon == resTCon
          -- indicesTele = Δ
          -- argsTele    = Δ'm
          (_,indicesTele, AConstructorDef _ argsTele) <- lookupDCon c
          b's <-pure $ map (\i -> ANthEq i b) [0 .. aTeleLength indicesTele - 1]
          v's <- casepush indicesTele srcIndices resIndices b's
                          vs argsTele
          stepBareCase (ADCon c th resIndices v's) eqname matches ty
  where
    casepush (aTeleNames -> xs) src res bs vs0 tele'0 =
      reverse . fst <$> go (reverse vs0) (reverse $ aTeleList tele'0)
      where
        go [] [] = return ([],[])
        go ((v,eps):vs) ((y,e,eps'):tele') | eps == eps' = do
          (v's,ys) <- go vs tele'
          let b's = zipWith (\(vi,epsi) (v'i,_) -> AJoin vi 0 v'i 0 CBV) vs v's
              v'  = AConv v
                          (ACong (bs ++ b's)
                                 (bind (xs ++ ys) e)
                                 (ATyEq 
                                        (substs (zip xs src ++ zip ys (map fst vs) ) e)
                                        (substs (zip xs res ++ zip ys (map fst v's)) e)
                                    ))
          return $ ((v',eps) : v's, y : ys)
        go _ _ = mzero
    
    aTeleNames = map (\(y,_,_) -> y) . aTeleList
    
    aTeleList AEmpty = []
    aTeleList (ACons (unrebind -> ((y,  unembed -> e,  eps),  tele'))) =
      (y,e,eps) : aTeleList tele'
stepCase scrut eqname matches ty = stepBareCase scrut eqname matches ty

-- Beta-reduce a case expression (the arguments are scrutinee, equation name, branches, type of the entire case expression)
-- "Bare" means that this doesn't handle the case when the redex is blocked by an AConv
stepBareCase :: ATerm -> AName -> [AMatch] -> ATerm -> MaybeT TcMonad ATerm
stepBareCase (eraseToHead -> AAbort _) _ _ ty = return $ AAbort ty
stepBareCase cval@(ADCon c _ _ args) eqname matches ty = do
  AMatch _ matchBodyBnd <- MaybeT . return $
                             find (\(AMatch c' _) -> c == c') matches
  (delta, matchBody) <- unbind matchBodyBnd
  guardExpected $ aTeleLength delta == length args
  return $
    subst eqname (AReflEq cval) $ 
        substATele delta (map fst args) matchBody
stepBareCase _ _ _ _ = mzero

  
-- Step the term for at most n steps, or until it is stuck.
asteps :: Int -> ATerm -> TcMonad ATerm
asteps 0 a = return a
asteps n a = do
  ma' <- aRealStep a
  case ma' of
    Nothing -> return a
    Just a' -> asteps (n-1) a'

-- For debugging purposes during development, 
-- we wrap aRealParStep in this checking function. 
aParStep :: Bool -> ATerm -> TcMonad ATerm
aParStep deep a = do
  aE <- erase a
  aE' <- parStep deep aE
  a' <- aRealParStep deep a
  a'E <- erase a'
  unless (aE' `aeq` a'E) $
    warn [DS "Internal error: reduction mismatch for the expression", DD a,
          DS "which erases to", DD aE,
          DS "parStep steps to", DD aE',
          DS "aParStep steps to", DD a',
          DS "which erases to", DD a'E ]
  return a'

-- type-preserving parallel reduction relation.
-- See OpSem.hs for an unannotated version, which may be easier to understand at first.
aRealParStep :: Bool -> ATerm -> TcMonad ATerm
aRealParStep deep a@(AVar x) = do
  def <- lookupDef x
  case def of
   Nothing -> return a
   Just b -> return b  
aRealParStep deep a@(AUniVar _ _) = return a
aRealParStep deep (ACumul a i) = ACumul <$> aParStep deep a <*> pure i 
aRealParStep deep a@(AType _) = return a
aRealParStep deep a@(ATCon c idxs) = ATCon c <$> mapM (aParStep deep) idxs
aRealParStep deep a@(ADCon c th params args) | any (isAAbort.eraseToHead.fst) args = do 
  (_,ty ) <- getType a
  return (AAbort ty)
aRealParStep deep (ADCon c th params args) = ADCon c th params <$> mapM (firstM (aParStep deep)) args
aRealParStep deep (AArrow lvl ex ep bnd) = do
  ((x, unembed->a), b) <- unbind bnd
  a' <- aParStep deep a
  b' <- extendCtx (ASig x Program a) $ aParStep True b
  return $ AArrow lvl ex ep (bind (x,embed a') b') 
aRealParStep deep (ALam th ty@(eraseToHead -> (AArrow _ _ _ bndTy)) ep bnd) = do
  Just ((x , unembed -> aTy), bTy , _, b) <- unbind2 bndTy bnd
  ALam th ty ep <$> (bind x <$> (extendCtx (ASig x Program aTy) $ aParStep True b))
aRealParStep deep (ALam _ _ _ _) = err [DS "internal error: Lam with wrong type annotation in aParStep"]

-- Todo: Hm, I think this doesn't quite match parStep when b is erased, since it will not step?
aRealParStep deep (AApp ep a b ty) = do
 stepped <- runMaybeT (stepFun deep a b ty)
 case (stepped, ep) of 
   (Just res, _) -> return res
   (Nothing, Erased)  -> AApp Erased <$> aParStep deep a <*> pure b <*> pure ty
   (Nothing, Runtime) -> AApp Runtime <$> aParStep deep a <*> aParStep deep b <*> pure ty  --TODO: this is not right, we need to insert a conv as well.
aRealParStep deep a@(AAt _ _) = return a
aRealParStep deep (AUnbox a) = do
  stepped <- runMaybeT (stepUnbox a)
  case stepped of 
    Just res -> return res
    Nothing -> AUnbox <$> aParStep deep a
aRealParStep deep (ABox a th) = ABox <$> aParStep deep a <*> pure th
aRealParStep deep a@(AAbort t) = return a
aRealParStep deep (ATyEq a b) = ATyEq <$> aParStep deep a <*> aParStep deep b
aRealParStep deep a@(AJoin _ _ _ _ _) = return a
aRealParStep deep a@(ACong _ _ _) = return a
aRealParStep deep (AConv a p) = do
  stepped <- runMaybeT (stepConv a p)
  case stepped of  
    Just res -> return res
    Nothing -> AConv <$> aParStep deep a <*> pure p
aRealParStep deep a@(AInjDCon _ _) = return a
aRealParStep deep a@(AContra _ _) = return a
aRealParStep deep a@(ASmaller _ _) = return a
aRealParStep deep a@(AOrdAx _ _) = return a
aRealParStep deep a@(AOrdTrans _ _) = return a
aRealParStep deep a@(AInd ty bnd) = do
  underInd a
           (\f xs body bodyTy -> do
               body' <- aParStep True body
               return $ AInd ty (bind (f,xs) body'))
aRealParStep deep a@(ARec ty bnd) = do
  underRec a
           (\f xs body bodyTy -> do
              body' <- aParStep True body
              return $ ARec ty (bind (f,xs) body'))
aRealParStep deep (ALet Runtime bnd (th,ty)) = do
  ((_, _, unembed -> a), _) <- unbind bnd
  underLet (ALet Runtime bnd (th,ty))
           (\x xeq b -> do
             case a of
               (AAbort _) -> return $ AAbort ty
               _          -> do 
                 aval <- isConvAValue a
                 if aval
                   --TODO: this is not right, we need to substitute a different proof for xeq as well.
                   then return $ subst x a b
                   else do 
                     a' <- aParStep deep a
                     b' <- aParStep True b
                     return $ ALet Runtime (bind (x, xeq, embed a') b') (th,ty))
aRealParStep deep (ALet Erased bnd (th,ty)) = do
  ((_, _, unembed -> a), _) <- unbind bnd
  underLet (ALet Erased bnd (th,ty))
           (\x xeq b -> do
              subst x a <$> aParStep True b)
--TODO: rewrite in terms of underCase
aRealParStep deep (ACase a bnd (th,ty)) = do
  (eqname, matches) <- unbind bnd
  stepped <- runMaybeT (stepCase a eqname matches ty)
  case stepped of
    Just res -> return res
    -- TODO: This is not right, need to substitute a different proof for eqname.
    Nothing -> do
       a' <- aParStep deep a
       matches' <- mapM aParStepMatch matches
       return $ ACase a' (bind eqname matches') (th,ty)
 where aParStepMatch (AMatch c mtchBnd) = do
         (xs, body) <- unbind mtchBnd
         body' <- aParStep True body
         return (AMatch c (bind xs body'))
aRealParStep deep a@(ADomEq _) = return a
aRealParStep deep a@(ARanEq _ _ _) = return a
aRealParStep deep a@(AAtEq  _) = return a
aRealParStep deep a@(ANthEq _ _) = return a
aRealParStep deep a@(ATrustMe _) = return a
aRealParStep deep (AHighlight a) = AHighlight <$> aParStep deep a
aRealParStep deep a@(AReflEq _) = return a
aRealParStep deep a@(ASymEq _) = return a
aRealParStep deep a@(ATransEq _ _) = return a
aRealParStep deep a@(AEraseEq _) = return a

-- Step the term for at most n steps, or until it is stuck.
aParSteps :: Int -> ATerm -> TcMonad ATerm
aParSteps 0 a = return a
aParSteps n a = do 
 a' <- aParStep False a 
 if (a `aeq` a')
  then return a 
  else aParSteps (n-1) a'

isAAbort :: ATerm -> Bool
isAAbort (AAbort _) = True
isAAbort _ = False

firstM :: Monad m => (a -> m b) -> (a,c) -> m (b,c)
firstM f (x,y) = do
  x' <- f x
  return (x',y)

guardExpected :: (MonadReader Env m, MonadIO m, MonadPlus m) => Bool -> m ()
guardExpected True = return ()
guardExpected False = warn [DS "Internal error: annotated reduction encountered illtyped term?"]
