{-# LANGUAGE ViewPatterns, TupleSections #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.AOpSem
  ( isPlainAValue, isConvAValue
  , symEq, transEq
  , astep, asteps)
where

import Language.Trellys.Syntax
import Language.Trellys.Environment (lookupDCon, lookupDef)
import Language.Trellys.TypeMonad
import Language.Trellys.GenericBind
import Language.Trellys.TypeCheckCore
import Language.Trellys.OpSem

--Stuff used for debugging.
 {-
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ ( (<>), (<+>),hsep,text, parens, brackets, nest, render)
 -}

import Unbound.LocallyNameless.Types (GenBind)

import Control.Applicative
import Control.Monad.Writer hiding (join)
import Control.Monad.Trans.Maybe
import Data.List

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


-- If eps == Erased, don't bother stepping.

astep :: ATerm -> TcMonad (Maybe ATerm)
astep (AVar x) = lookupDef x
astep (AUniVar _ _) = return Nothing
astep (ACumul a i) = fmap (flip ACumul i) <$> astep a
astep (AType _) = return Nothing
astep (ATCon _ _) = return Nothing
astep (ADCon c th annots argsOrig) = stepArgs [] argsOrig
  where stepArgs  _     []               = return Nothing
        stepArgs prefix ((arg,eps):args) = do
          stepArg <- astep arg
          case stepArg of
            Nothing         -> stepArgs ((arg,eps):prefix) args
            Just (AAbort t) -> return . Just $ AAbort t
            Just arg'       -> return . Just . ADCon c th annots $
                                 reverse prefix ++ (arg',eps) : args
astep (AArrow _ _ _ _) = return Nothing
astep (ALam _ _ _ _) = return Nothing
astep (AApp eps a b ty) = do
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ AApp eps a' b ty
    Nothing         -> do
      aval <- isConvAValue a
      if not aval
        then do 
          return Nothing
        else do
          stepB <- astep b
          case stepB of
            Just b'         -> return . Just $ AApp eps a b' ty
            Nothing         -> runMaybeT $ stepFun a b ty 
astep (AAt _ _) = return Nothing
astep (AUnbox a) = do
  stepA <- astep a
  case stepA of
    Just a'         -> return . Just $ AUnbox a'
    Nothing         -> runMaybeT $ stepUnbox a
astep (ABox a th) = fmap (flip ABox th) <$> astep a
astep (AAbort t) = return Nothing
astep (ATyEq _ _) = return Nothing
astep (AJoin _ _ _ _ _) = return Nothing
astep (ACong _ _ _) = return Nothing
astep (AConv a p) = do
  stepA <- astep a
  case stepA of
    Just a'         -> return . Just $ AConv a' p
    Nothing         -> do
      runMaybeT $ stepConv a p
astep (AInjDCon _ _) = return Nothing
astep (AContra _ _) = return Nothing
astep (ASmaller _ _) = return Nothing
astep (AOrdAx _ _) = return Nothing
astep (AOrdTrans _ _) = return Nothing
astep (AInd _ _) = return Nothing
astep (ARec _ _) = return Nothing
astep (ALet eps bnd annot) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ ALet eps (bind (x, xeq, embed a') b) annot
    Nothing         -> do
      aval <- isConvAValue a
      if not aval
        then return Nothing
        else return . Just $ subst x a b
astep (ACase a bnd ty) = do
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ ACase a' bnd ty
    Nothing         -> runMaybeT $ do
      (eqname, matches) <- unbind bnd
      case a of
        cval@(ADCon c _ _ args) -> do
            AMatch _ matchBodyBnd <- MaybeT . return
                                  $  find (\(AMatch c' _) -> c == c') matches
            (delta, matchBody) <- unbind matchBodyBnd
            guard $ aTeleLength delta == length args
            return $
              subst eqname (AJoin cval 0 cval 0 CBV) $ 
                  substATele delta (map fst args) matchBody
        AConv (ADCon c th indices vs) b -> do
          (_, ATyEq (eraseToHead -> ATCon srcTCon srcIndices)
                    (eraseToHead -> ATCon resTCon resIndices)) <- lift $ getType b
          guard $ srcTCon == resTCon
          -- indicesTele = Δ
          -- argsTele    = Δ'm
          (_,indicesTele, AConstructorDef _ argsTele) <- lookupDCon c
          b's <-pure $ map (\i -> ANthEq i b) [0 .. aTeleLength indicesTele - 1]
          v's <- casepush indicesTele srcIndices resIndices b's
                          vs argsTele
          return $ ACase (ADCon c th resIndices v's) bnd ty
        _ -> mzero
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
                                 (ATyEq (substs (zip xs src ++ zip ys (map fst vs) ) e)
                                        (substs (zip xs res ++ zip ys (map fst v's)) e)))
          return $ ((v',eps) : v's, y : ys)
        go _ _ = mzero
    
    aTeleNames = map (\(y,_,_) -> y) . aTeleList
    
    aTeleList AEmpty = []
    aTeleList (ACons (unrebind -> ((y,  unembed -> e,  eps),  tele'))) =
      (y,e,eps) : aTeleList tele'
astep (ADomEq _) = return Nothing
astep (ARanEq p a a') = return Nothing
astep (AAtEq  _) = return Nothing
astep (ANthEq _ _) = return Nothing
astep (ATrustMe _) = return Nothing
astep (AHighlight a) = astep a
astep (AReflEq _) = return Nothing
astep (ASymEq _) = return Nothing
astep (ATransEq _ _) = return Nothing
astep (AEraseEq _) = return Nothing

-- Beta-reduce an application of a lam, rec, or ind, possibly under a bunch of conversions.
-- The last ATerm is the type of the entire application.
stepFun :: ATerm -> ATerm -> ATerm -> MaybeT TcMonad ATerm
stepFun (eraseToHead -> AAbort _) _  ty = return $ AAbort ty
stepFun _ (eraseToHead -> AAbort _)  ty = return $ AAbort ty
-- If a is a converted value we have to do something smart.
stepFun (AConv funv p) b ty = do
  --liftIO $ putStrLn . render . disp $ [DS "About to try to step", DD (AConv funv p),
  --                                     DS "applied to", DD b]
  (_, ATyEq (AArrow si srcEx srcEps srcTyBnd)
            (AArrow ri resEx resEps resTyBnd)) <- lift $ getType p
  guard $ si == ri                                           
  guard $ srcEps == resEps
  do -- Scoping
  ( (tyVar, unembed -> srcDom), srcRan,
    (_,     unembed -> resDom), resRan ) <- unbind2M srcTyBnd resTyBnd                        
  let convInput :: ATerm -> ATerm
      convInput v =       AConv v (ADomEq p)  {- :: srcDom -}
  let convOutput :: ATerm {- the input value -}
                    -> ATerm {- the body -}
                    -> ATerm
      convOutput v body = AConv body (ARanEq p (convInput v) v) {- :: (subst tyVar v resRan) -}
  convOutput b <$> stepBareFun funv (convInput b)
-- Otherwise, if a is not a converted value, it is either a function value or the 
-- application is stuck, so we let stepBareFun do its thing.
stepFun a b ty = stepBareFun a b

-- Beta-reduce an application of a lam, rec, or ind.
-- "Bare" means that this function doesn't handle the case when an AConv blocks the redex.
stepBareFun :: ATerm -> ATerm -> MaybeT TcMonad ATerm
stepBareFun (ALam _ _ _ bnd) b = do
  guard =<< (isEValue <$> erase b)
  (x,body) <- unbind bnd
  return  $ subst x b body
stepBareFun a@(ARec _ty bnd) b = do
  guard =<< (isEValue <$> erase b)
  ((f,[(x,ep)]),body) <- unbind bnd   --TODO: n-ary rec
  return $ subst f a $ subst x b body
stepBareFun a@(AInd (eraseToHead -> AArrow i ex epsArr tyBnd) bnd) b = do
  guard =<< (isEValue <$> erase b)
  -- We can't use unbind2 here, because bnd and tyBnd have
  -- different numbers of variables.
  --TODO: generalize to n-ary ind.
  ((f,[(x,_xep)]),body)           <- unbind bnd   --TODO: n-ary ind
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
stepBareFun _ _ = mzero

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
-- TODO: maybe it would be better to make this into the other step* functions instead. 
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
  
-- Step the term for at most n steps, or until it is stuck.
asteps :: Int -> ATerm -> TcMonad ATerm
asteps 0 a = return a
asteps n a = do
  ma' <- astep a
  case ma' of
    Nothing -> return a
    Just a' -> asteps (n-1) a'
-- type-preserving parallel reduction relation.
-- See OpSem.hs for an unannotated version, which may be easier to understand at first.
aParStep :: Bool -> ATerm -> TcMonad ATerm
aParStep deep a@(AVar x) = do
  def <- lookupDef x
  case def of
   Nothing -> return a
   Just b -> return b  
aParStep deep a@(AUniVar _ _) = return a
aParStep deep (ACumul a i) = ACumul <$> aParStep deep a <*> pure i 
aParStep deep a@(AType _) = return a
aParStep deep a@(ATCon _ _) = return a
aParStep deep a@(ADCon c th params args) | any (isAAbort.eraseToHead.fst) args = do --TODO: there should be some better way here.
  (_,ty ) <- getType a
  return (AAbort ty)
aParStep deep (ADCon c th params args) = ADCon c th params <$> mapM (firstM (aParStep deep)) args
aParStep deep (AArrow lvl ex ep bnd) = do
  ((x, unembed->a), b) <- unbind bnd
  a' <- aParStep deep a
  b' <- aParStep True b
  return $ AArrow lvl ex ep (bind (x,embed a') b') 
aParStep deep (ALam th ty ep bnd) = do
  (x, b) <- unbind bnd 
  ALam th ty ep <$> (bind x <$> aParStep True b)
aParStep deep (AApp ep a b ty) = do
  a' <- aParStep deep a
  b' <- aParStep deep b
  stepped <- runMaybeT (stepFun a' b' ty)
  case stepped of
    Nothing -> return (AApp ep a' b' ty)
    Just res -> return res
aParStep deep a@(AAt _ _) = return a
aParStep deep (AUnbox a) = do
  a' <- aParStep deep a
  stepped <- runMaybeT (stepUnbox a')
  case stepped of 
    Nothing -> return (AUnbox a')
    Just res -> return res
aParStep deep (ABox a th) = ABox <$> aParStep deep a <*> pure th
aParStep deep a@(AAbort t) = return a
aParStep deep (ATyEq a b) = ATyEq <$> aParStep deep a <*> aParStep deep b
aParStep deep a@(AJoin _ _ _ _ _) = return a
aParStep deep a@(ACong _ _ _) = return a
aParStep deep (AConv a p) = do
  a' <- aParStep deep a
  stepped <- runMaybeT (stepConv a' p)
  case stepped of  
    Nothing -> return (AConv a' p)
    Just res -> return res
aParStep deep a@(AInjDCon _ _) = return a
aParStep deep a@(AContra _ _) = return a
aParStep deep a@(ASmaller _ _) = return a
aParStep deep a@(AOrdAx _ _) = return a
aParStep deep a@(AOrdTrans _ _) = return a
aParStep deep a@(AInd _ _) = return a
aParStep deep a@(ARec _ _) = return a
aParStep deep (ALet eps bnd (th,ty)) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  a' <- aParStep deep a
  b' <- aParStep True b
  case a' of
    (AAbort _) -> return $ AAbort ty
    _          -> do 
      aval <- isConvAValue a
      --TODO: this is actually not right, we need to substitute a different proof for xeq as well.
      if not aval
        then return $ ALet eps (bind (x, xeq, embed a') b') (th,ty)
        else return $ subst x a' b'

{-
aParStep (ACase a bnd ty) = do
  stepA <- aParStep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ ACase a' bnd ty
    Nothing         -> runMaybeT $ do
      (eqname, matches) <- unbind bnd
      case a of
        cval@(ADCon c _ _ args) -> do
            AMatch _ matchBodyBnd <- MaybeT . return
                                  $  find (\(AMatch c' _) -> c == c') matches
            (delta, matchBody) <- unbind matchBodyBnd
            guard $ aTeleLength delta == length args
            return $
              subst eqname (AJoin cval 0 cval 0 CBV) $ 
                  substATele delta (map fst args) matchBody
        AConv (ADCon c th indices vs) b -> do
          (_, ATyEq (eraseToHead -> ATCon srcTCon srcIndices)
                    (eraseToHead -> ATCon resTCon resIndices)) <- lift $ getType b
          guard $ srcTCon == resTCon
          -- indicesTele = Δ
          -- argsTele    = Δ'm
          (_,indicesTele, AConstructorDef _ argsTele) <- lookupDCon c
          b's <-pure $ map (\i -> ANthEq i b) [0 .. aTeleLength indicesTele - 1]
          v's <- casepush indicesTele srcIndices resIndices b's
                          vs argsTele
          return $ ACase (ADCon c th resIndices v's) bnd ty
        _ -> mzero
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
                                 (ATyEq (substs (zip xs src ++ zip ys (map fst vs) ) e)
                                        (substs (zip xs res ++ zip ys (map fst v's)) e)))
          return $ ((v',eps) : v's, y : ys)
        go _ _ = mzero
    
    aTeleNames = map (\(y,_,_) -> y) . aTeleList
    
    aTeleList AEmpty = []
    aTeleList (ACons (unrebind -> ((y,  unembed -> e,  eps),  tele'))) =
      (y,e,eps) : aTeleList tele'
aParStep (ADomEq _) = return Nothing
aParStep (ARanEq p a a') = return Nothing
aParStep (AAtEq  _) = return Nothing
aParStep (ANthEq _ _) = return Nothing
aParStep (ATrustMe _) = return Nothing
aParStep (AHighlight a) = aParStep a
aParStep (AReflEq _) = return Nothing
aParStep (ASymEq _) = return Nothing
aParStep (ATransEq _ _) = return Nothing
aParStep (AEraseEq _) = return Nothing
-}


isAAbort :: ATerm -> Bool
isAAbort (AAbort _) = True
isAAbort _ = False

firstM :: Monad m => (a -> m b) -> (a,c) -> m (b,c)
firstM f (x,y) = do
  x' <- f x
  return (x',y)
