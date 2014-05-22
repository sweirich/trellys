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
            Just (AAbort t) -> return . Just $ AAbort t
            Just b'         -> return . Just $ AApp eps a b' ty
            Nothing         -> do
              bval <- isConvAValue b
              if not bval
                then do
                    return Nothing
                else case a of
                  -- If a is a converted value we have to do something smart.
                  AConv funv p -> do
                        --liftIO $ putStrLn . render . disp $ [DS "About to try to step", DD (AConv funv p),
                        --                                     DS "applied to", DD b]
                        (_, ATyEq (AArrow si srcEx srcEps srcTyBnd)
                                  (AArrow ri resEx resEps resTyBnd)) <- getType p
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
                        runMaybeT $ 
                           convOutput b <$> stepFun funv (convInput b)
                  -- Otherwise, if a is not a converted value, it is either a function value or the 
                  -- application is stuck, so we let stepFun do its thing.
                  _ -> do
                         runMaybeT (stepFun a b)

astep (AAt _ _) = return Nothing

astep (AUnbox a) = do
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ AUnbox a'
    Nothing         -> case a of
      ABox a' th  ->
        return $ Just a'
      AConv (ABox v th) p ->
            return . Just
                   . AUnbox
                   $ ABox (AConv v (AAtEq p)) th
      _ ->

        return Nothing

astep (ABox a th) = fmap (flip ABox th) <$> astep a

astep (AAbort t) = return Nothing

astep (ATyEq _ _) = return Nothing

astep (AJoin _ _ _ _ _) = return Nothing

astep (ACong _ _ _) = return Nothing

astep (AConv a p) = do
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ AConv a' p
    Nothing         -> do
      aval <- isConvAValue a
      case a of
        AConv v q | aval -> do
          (_, ATyEq ty1 ty2) <- getType q
          (_, ATyEq ty2' ty3) <- getType p
          pq <- (transEq ty1 ty2 ty3 q p)
          return . Just $ AConv v pq
        _ -> return Nothing
  
astep (AInjDCon _ _) = return Nothing

astep (AContra _ _) = return Nothing

astep (ASmaller _ _) = return Nothing

astep (AOrdAx _ _) = return Nothing

astep (AOrdTrans _ _) = return Nothing

astep (AInd _ _ _) = return Nothing

astep (ARec _ _ _) = return Nothing

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

-- Beta-reduce an application of a lam, rec, or ind.
stepFun :: ATerm -> ATerm -> MaybeT TcMonad ATerm
stepFun (ALam _ _ _ bnd) b = do
  (x,body) <- unbind bnd
  return  $ subst x b body
stepFun a@(ARec _ _ bnd) b = do
  ((f,x),body) <- unbind bnd
  return $ subst f a $ subst x b body
stepFun a@(AInd (eraseToHead -> AArrow i ex epsArr tyBnd) _ bnd) b = do
  -- We can't use unbind2 here, because bnd and tyBnd have
  -- different numbers of variables.
  ((f,x),body)                    <- unbind bnd
  ( (tyVar,unembed -> ty1), ty2 ) <- unbind tyBnd
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
stepFun _ _ = mzero


-- Step the term for at most n steps, or until it is stuck.
asteps :: Int -> ATerm -> TcMonad ATerm
asteps 0 a = return a
asteps n a = do
  ma' <- astep a
  case ma' of
    Nothing -> return a
    Just a' -> asteps (n-1) a'

