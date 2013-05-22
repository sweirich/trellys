{-# LANGUAGE ViewPatterns, TupleSections #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.AOpSem
  ( isPlainAValue, isConvAValue
  , Correspondence(..), correspondingVarName, symEq, composeEq, disunify
  , astep)
where

import Language.Trellys.Syntax
import Language.Trellys.Environment (lookupDCon)
import Language.Trellys.TypeMonad
import Language.Trellys.GenericBind
import Language.Trellys.TypeCheckCore
import Language.Trellys.OpSem

import Unbound.LocallyNameless.Types (GenBind)
import Control.Applicative
import Control.Monad.Writer hiding (join)
import Control.Monad.Trans.Maybe
import Data.List
import Data.Ord
import qualified Data.Map as M

isPlainAValue :: (Fresh m, Applicative m) => ATerm -> m Bool
isPlainAValue = fmap isEValue . erase

isConvAValue :: (Fresh m, Applicative m) => ATerm -> m Bool
isConvAValue (AConv a _ _ _) = isPlainAValue a
isConvAValue a               = isPlainAValue a

{------------------------------------------------------------------------------}

data Correspondence = LeftVar  AName
                    | RightVar AName
                    | TwoVars  AName AName AName
                      -- left right new
                    deriving (Eq, Ord, Show)

correspondingVarName :: Correspondence -> AName
correspondingVarName (LeftVar  l)       = l
correspondingVarName (RightVar r)       = r
correspondingVarName (TwoVars  _ _ y'') = y''

-- symEq A B (pAB : A = B) : B = A
symEq :: Fresh m => ATerm -> ATerm -> ATerm -> m ATerm
symEq a b pab = do
  x <- fresh $ string2Name "x"
  return . AConv (AJoin a 0 a 0) [(pab,Erased)] (bind [x] $ ATyEq (AVar x) a) $ ATyEq b a

-- composeEq A C (pAB : A = B) (pBC : B = C) : A = C
composeEq :: Fresh m => ATerm -> ATerm -> ATerm -> ATerm -> m ATerm
composeEq a c pab pbc = do
  x <- fresh $ string2Name "x"
  return . AConv pab [(pbc,Erased)] (bind [x] . ATyEq a $ AVar x) $ ATyEq a c

unbind2M :: (MonadPlus m, Fresh m, Alpha p1, Alpha p2, Alpha t1, Alpha t2)
         => GenBind order card p1 t1
         -> GenBind order card p2 t2
         -> m (p1, t1, p2, t2)
unbind2M bnd bnd' = maybe mzero return =<< unbind2 bnd bnd'

-- Precondition: all the ANames are fresh.  If we had
--   conv a by b1 ... bM at x1 ... xM . A : B
-- and
--   conv a' by b1' ... bN' at x1' ... xN' . A' : B'
-- then we generate brand new y1 .. yM and x1' ... xN' and substitute in for
-- them.  This means they will never collide, and so we don't need to grow or
-- shrink the lists.
disunify :: [AName] -> ATerm -> [AName] -> ATerm
         -> WriterT [Correspondence]
                    (MaybeT TcMonad)
                    ATerm
disunify ls l0 rs r0 = go l0 r0
  where
    go (AVar l) (AVar r)
      | l `elem` ls && r `elem` rs = do
        y'' <- fresh $ string2Name "y''"
        AVar y'' <$ tell [TwoVars l r y'']

    go (AVar l) r
      | l `elem` ls = AVar l <$ tell [LeftVar l]
    
    go l (AVar r)
      | r `elem` rs = AVar r <$ tell [RightVar r]

    go (AVar x) (AVar x') | x == x' =
      pure $ AVar x
    
    go (AUniVar l a) (AUniVar r a')
      | l `elem` ls && r `elem` rs = do
        y'' <- fresh $ string2Name "y''"
        tell [TwoVars l r y'']
        AUniVar l <$> go a a'
    
    go (AUniVar l a) r
      | l `elem` ls = AUniVar l a <$ tell [LeftVar l]
    
    go l (AUniVar r a')
      | r `elem` rs = do
        AUniVar r a' <$ tell [RightVar r]
    
    go (AUniVar x a) (AUniVar x' a') | x == x' =
      AUniVar x <$> go a a'
    
    go (ACumul a i) (ACumul a' i') | i == i' =
      ACumul <$> go a a' <*> pure i
    
    go (AType i) (AType i') | i == i' =
      pure $ AType i

    go (ATCon d as) (ATCon d' as')
      | d == d' && length as == length as' =
        ATCon d <$> zipWithM go as as'
    
    go (ADCon d as bs) (ADCon d' as' bs')
      | d == d' && length as == length as' && length bs == length bs' =
        ADCon d <$> zipWithM go as as'
                <*> zipWithM (\(b,eps) (b',eps') -> do
                                 guard $ eps == eps'
                                 b'' <- go b b'
                                 pure (b'',eps))
                             bs bs'

    go (AArrow ex eps bnd) (AArrow _ eps' bnd') | eps == eps' = do
      ((x, unembed -> dom), ran, (_, unembed -> dom'), ran') <- unbind2M bnd bnd'
      dom'' <- go dom dom'
      ran'' <- go ran ran'
      pure . AArrow ex eps $ bind (x, embed dom'') ran''
    
    go (ALam ty eps bnd) (ALam ty' eps' bnd') | eps == eps' = do
      (x,body,_,body') <- unbind2M bnd bnd'
      ty''             <- go ty ty'
      body''           <- go body body'
      pure . ALam ty'' eps $ bind x body''
    
    go (AApp eps a b t) (AApp eps' a' b' t') | eps == eps' =
      AApp eps <$> go a a' <*> go b b' <*> go t t'
    
    go (AAt a th) (AAt a' th') | th == th' =
      AAt <$> go a a' <*> pure th
    
    go (AUnboxVal a) (AUnboxVal a') =
      AUnboxVal <$> go a a'
    
    go (ABox a th) (ABox a' th') | th == th' =
      ABox <$> go a a' <*> pure th
    
    go (AAbort a) (AAbort a') =
      AAbort <$> go a a'
    
    go (ATyEq a b) (ATyEq a' b') =
      ATyEq <$> go a a' <*> go b b'
    
    go (AJoin a i b j) (AJoin a' i' b' j') | i == i' && j == j' =
      AJoin <$> go a a' <*> pure i <*> go b b' <*> pure j
    
    go (AConv a bs bnd res) (AConv a' bs' bnd' res') | length bs == length bs' = do
      (xs, template, xs', template') <- unbind2M bnd bnd'
      guard $ length xs == length xs' -- This is the only reason we bring xs' in scope
      template'' <- go template template'
      AConv <$> go a a'
            <*> (zipWithM (\(b,eps) (b',eps') -> do
                              guard $ eps == eps'
                              b'' <- go b b'
                              pure (b'',eps))
                          bs bs')
            <*> pure (bind xs template'')
            <*> go res res'
    
    go (AInjDCon a i) (AInjDCon a' i') | i == i' =
      AInjDCon <$> go a a' <*> pure i
    
    go (AContra a b) (AContra a' b') =
      AContra <$> go a a' <*> go b b'
    
    go (ASmaller a b) (ASmaller a' b') =
      ASmaller <$> go a a' <*> go b b'
    
    go (AOrdAx a b) (AOrdAx a' b') =
      AOrdAx <$> go a a' <*> go b b'
    
    go (AOrdTrans a b) (AOrdTrans a' b') =
      AOrdTrans <$> go a a' <*> go b b'
    
    go (AInd ty eps bnd) (AInd ty' eps' bnd') | eps == eps' = do
      ((f,x), body, _, body') <- unbind2M bnd bnd'
      body''                  <- go body body'
      AInd <$> go ty ty'
           <*> pure eps
           <*> pure (bind (f,x) body'')
    
    go (ARec ty eps bnd) (ARec ty' eps' bnd') | eps == eps' = do
      ((f,x), body, _, body') <- unbind2M bnd bnd'
      body''                  <- go body body'
      ARec <$> go ty ty'
           <*> pure eps
           <*> pure (bind (f,x) body'')
    
    go (ALet eps bnd) (ALet eps' bnd') | eps == eps' = do
      ((x, y, unembed -> a), b, (_, _, unembed -> a'), b') <- unbind2M bnd bnd'
      a'' <- go a a'
      b'' <- go b b'
      pure . ALet eps $ bind (x, y, embed a'') b''
     
    go (ACase a bnd ty) (ACase a' bnd' ty') = do
      let sortArms = sortBy (comparing $ \(AMatch c _) -> c)
      (x, sortArms -> arms, _, sortArms -> arms') <- unbind2M bnd bnd'
      guard $ length arms == length arms'
      let goMatch (AMatch c teleBnd) (AMatch c' teleBnd') = do
            (tele,  body)  <- unbind teleBnd
            (tele', body') <- unbind teleBnd'
            tele'' <- goTele tele tele'
            body'' <- go body body'
            pure . AMatch c $ bind tele'' body
          -- WRONG: Do more substitution!
          goTele AEmpty AEmpty =
            pure AEmpty
          -- There doesn't seem to be an unrebind2
          goTele (ACons (unrebind -> ((y,  unembed -> b,  eps),  teleTail )))
                 (ACons (unrebind -> ((y', unembed -> b', eps'), teleTail')))
            | eps == eps' = do
              b''        <- go b b'
              teleTail'' <- goTele teleTail $ subst y (AVar y') teleTail'
              pure . ACons $ rebind (y, embed b'', eps) teleTail''
          goTele _ _ =
            mzero
      arms'' <- zipWithM goMatch arms arms'
      ACase <$> go a a'
            <*> pure (bind x arms'')
            <*> go ty ty'
    
    go (ADomEq a) (ADomEq a') =
      ADomEq <$> go a a'
    
    go (ARanEq a b) (ARanEq a' b') =
      ARanEq <$> go a a' <*> go b b'
    
    go (AAtEq a) (AAtEq a') =
      AAtEq <$> go a a'
    
    go (ANthEq i a) (ANthEq i' a') | i == i' =
      ANthEq i <$> go a a'
    
    go (ATrustMe a) (ATrustMe a') =
      go a a'

    go (ASubstitutedFor a x) (ASubstitutedFor a' x') | x == x' =
      ASubstitutedFor <$> go a a' <*> pure x'
    
    go _ _ =
      mzero

-- If eps == Erased, don't bother stepping.

astep :: ATerm -> TcMonad (Maybe ATerm)

astep (AVar _) = return Nothing

astep (AUniVar _ _) = return Nothing

astep (ACumul a i) = fmap (flip ACumul i) <$> astep a

astep (AType _) = return Nothing

astep (ATCon _ _) = return Nothing

astep (ADCon c annots argsOrig) = stepArgs [] argsOrig
  where stepArgs  _     []               = return Nothing
        stepArgs prefix ((arg,eps):args) = do
          stepArg <- astep arg
          case stepArg of
            Nothing         -> stepArgs ((arg,eps):prefix) args
            Just (AAbort t) -> return . Just $ AAbort t
            Just arg'       -> return . Just . ADCon c annots $
                                 reverse prefix ++ (arg',eps) : args

astep (AArrow _ _ _) = return Nothing

astep (ALam _ _ _) = return Nothing

astep (AApp eps a b ty) = do
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ AApp eps a' b ty
    Nothing         -> do
      aval <- isConvAValue a
      if not aval
        then return Nothing
        else do
          stepB <- astep b
          case stepB of
            Just (AAbort t) -> return . Just $ AAbort t
            Just b'         -> return . Just $ AApp eps a b' ty
            Nothing         -> do
              bval <- isConvAValue b
              if not bval
                then return Nothing
                else case a of
                  AConv v bs convBnd (AArrow resEx resEps resTyBnd) -> do
                    let update updatee var newDom newRan mapBody = case updatee of
                          ALam src eps' bnd -> do
                            (x,body) <- unbind bnd
                            return . ALam newDom eps' . bind x $ mapBody body
                          ARec (eraseToHead -> AArrow tyEx tyEps tyBnd) eps' bnd -> do
                            ((f,recVar),rawBody) <- unbind bnd
                            ((tyVar,unembed -> dom),rawRan) <- unbind tyBnd
                            let body = subst recVar (AVar var) rawBody
                            return $ ARec (AArrow tyEx tyEps $ bind (var,embed newDom) newRan)
                                          eps'
                                          (bind (f,var) $ mapBody body)
                          AInd (eraseToHead -> AArrow tyEx tyEps tyBnd) eps' bnd -> do
                            ((f,recVar),rawBody) <- unbind bnd
                            ((tyVar,unembed -> dom),rawRan) <- unbind tyBnd
                            let body = subst recVar (AVar var) rawBody
                            return $ AInd (AArrow tyEx tyEps $ bind (var,embed newDom) newRan)
                                          eps'
                                          (bind (f,var) $ mapBody body)
                          _ -> mzero
                        
                        mkConv ps xs template res term = AConv term ps (bind xs template) res
                    (xs,template) <- unbind convBnd
                    runMaybeT $ case (template,xs,bs) of
                      (AVar x,[xx],[(p,pEps)]) | x == xx -> do
                        (_, ATyEq (AArrow srcEx  srcEps  srcTyBnd)
                                  (AArrow resEx' resEps' resTyBnd')) <- lift $ aTs p
                        guard $ srcEps == resEps
                        guard $ resEps == resEps'
                        do -- Scoping
                          ((x1, unembed -> dom1), ran1, (x2, unembed -> dom2), ran2) <-
                            unbind2M resTyBnd resTyBnd'
                          guard $ dom1 == dom2
                          guard $ ran1 == ran2
                        ( (tyVar, unembed -> srcDom), srcRan,
                          (_,     unembed -> resDom), resRan ) <- unbind2M srcTyBnd resTyBnd
                        x' <- fresh $ string2Name "x'"
                        x0 <- fresh $ string2Name "x"
                        x1 <- fresh $ string2Name "x"
                        symDom <- symEq srcDom resDom $ ADomEq p
                        let y' = AConv (AVar tyVar)
                                       [(symDom, pEps)]
                                       (bind [x'] $ AVar x')
                                       srcDom
                            p' = AConv p
                                       [ (ADomEq p, pEps)
                                       , (AJoin srcRan 0 (subst tyVar y' srcRan) 0, pEps) ]
                                       (bind [x0,x1] $
                                          ATyEq (AArrow srcEx srcEps $
                                                        bind (tyVar, embed $ AVar x0) (AVar x1))
                                                (AArrow resEx resEps $
                                                        bind (tyVar ,embed resDom) resRan)) 
                                       (ATyEq (AArrow srcEx srcEps $
                                                      bind (tyVar, embed resDom) $
                                                           subst tyVar y' srcRan)
                                              (AArrow resEx resEps $
                                                      bind (tyVar, embed resDom) resRan))
                        v' <- update (subst tyVar y' v) tyVar resDom resRan $
                                mkConv [(ARanEq p' $ AVar tyVar,pEps)]
                                       [x']
                                       (AVar x')
                                       resRan
                        return $ AApp eps v' b ty
                      (AArrow srcEx srcEps srcTyBnd,_,_) -> do
                        ( (tyVar, unembed -> srcDom), srcRan,
                          (_,     unembed -> resDom), resRan ) <- unbind2M srcTyBnd resTyBnd
                        let adjust f (bi,epsi) = do (b'i,t) <- f bi
                                                    return ((b'i,epsi),t)
                        (b's, froms) <- fmap unzip . forM bs . adjust $ \bi -> do
                                          (Logic, ATyEq fromTy toTy) <- lift $ aTs bi
                                          (fromTy,) <$> symEq fromTy toTy bi
                        let y' = AConv (AVar tyVar)
                                       b's
                                       (bind xs srcDom)
                                       (substs (zip xs froms) srcDom)
                        v' <- update (subst tyVar y' v) tyVar resDom resRan $
                                mkConv (bs ++ [(AJoin y' 0 (AVar tyVar) 0,Erased)])
                                       (xs ++ [tyVar])
                                       srcRan
                                       resRan
                        return $ AApp eps v' b ty
                      _ -> mzero
                  (ALam _ _ bnd) -> do
                    (x,body) <- unbind bnd
                    return . Just $ subst x b body
                  (ARec _ _ bnd) -> do
                    ((f,x),body) <- unbind bnd
                    return . Just . subst f a $ subst x b body
                  (AInd tyInd@(AArrow ex _ tyBnd) _ bnd) -> do
                    ((tyVar,ty1),ty2) <- unbind tyBnd
                    ((f,x),body) <- unbind bnd
                    y <- fresh $ string2Name "y"
                    p <- fresh $ string2Name "p"
                    let tyArr2 = AArrow ex Erased $ bind (p, embed $ ASmaller (AVar y) b) ty2
                        lam   = ALam (AArrow ex Runtime $ bind (tyVar,ty1) tyArr2) Runtime . bind y
                              . ALam tyArr2                                        Erased  . bind p
                              $ AApp Erased (AApp Runtime a (AVar y) tyInd) (AVar p) ty2
                    return . Just . subst f lam $ subst x b body
                  _ -> return Nothing

astep (AAt _ _) = return Nothing

astep (AUnboxVal a) = do
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ AUnboxVal a'
    Nothing         -> case a of
      ABox a' th  ->
        return $ Just a'
      AConv (ABox v th) bs convBnd (AAt tyRes th') | th == th' -> do
        (xs,template) <- unbind convBnd
        case (template,xs,bs) of
          (AVar x,[x'],[(b,eps)]) | x == x' -> do
            y <- fresh $ string2Name "y"
            return . Just
                   . AUnboxVal
                   $ ABox (AConv v [(AAtEq b,eps)] (bind [y] $ AVar y) tyRes)
                          th
          (AAt tyFrom th'',_,_) | th == th'' -> do
            return . Just $ AConv v bs (bind xs tyFrom) tyRes
          _ -> return Nothing
      _ ->
        return Nothing

astep (ABox a th) = fmap (flip ABox th) <$> astep a

astep (AAbort t) = return Nothing

astep (ATyEq _ _) = return Nothing

astep (AJoin _ _ _ _) = return Nothing

astep (AConv a bs bnd ty) = do
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ AConv a' bs bnd ty
    Nothing         -> do
      aval <- isConvAValue a
      case a of
        AConv v bs' bnd' ty' | aval -> do
          (xs,  template)  <- unbind bnd
          (xs', template') <- unbind bnd'
          ys  <- replicateM (length xs)  . fresh $ string2Name "y"
          ys' <- replicateM (length xs') . fresh $ string2Name "y'"
          mres <- runMaybeT . runWriterT $
                    disunify ys  (substs (zip xs  $ map AVar ys)  template)
                             ys' (substs (zip xs' $ map AVar ys') template')
          case mres of
            Nothing -> return Nothing -- XXX Should always succeed by soundness
            Just (template'', corrs) -> do
              let outers = M.fromList $ zip ys  bs
                  inners = M.fromList $ zip ys' bs'
                  eq :: Correspondence -> MaybeT TcMonad (ATerm,Epsilon)
                  eq (LeftVar  l)     = MaybeT . pure $ M.lookup l outers
                  eq (RightVar r)     = MaybeT . pure $ M.lookup r inners
                  eq (TwoVars  l r _) = do (oeq,oeps)        <- eq $ LeftVar  l
                                           (ieq,ieps)        <- eq $ RightVar r
                                           -- TODO: replace aTs with some getType function
                                           (_, ATyEq ta  tb) <- lift $ aTs ieq
                                           (_, ATyEq tb' tc) <- lift $ aTs oeq
                                           guard $ tb == tb'
                                             -- XXX Should always succeed by soundness
                                           eqtrans           <- composeEq ta tc ieq oeq
                                           pure (eqtrans, orEps oeps ieps)
                  bnd'' = bind (map correspondingVarName corrs) template''
              mbs'' <- runMaybeT $ mapM eq corrs
              case mbs'' of
                Just bs'' -> pure . Just $ AConv v bs'' bnd'' ty
                Nothing   -> pure Nothing
        _ -> return Nothing
  
astep (AInjDCon _ _) = return Nothing

astep (AContra _ _) = return Nothing

astep (ASmaller _ _) = return Nothing

astep (AOrdAx _ _) = return Nothing

astep (AOrdTrans _ _) = return Nothing

astep (AInd _ _ _) = return Nothing

astep (ARec _ _ _) = return Nothing

astep (ALet eps bnd) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just . ALet eps $ bind (x, xeq, embed a') b
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
      (_, matches) <- unbind bnd
      case a of
        ADCon c _ args -> do
            AMatch _ matchBodyBnd <- MaybeT . return
                                  $  find (\(AMatch c' _) -> c == c') matches
            (delta, matchBody) <- unbind matchBodyBnd
            guard $ aTeleLength delta /= length args
            return $ substATele delta (map fst args) matchBody
        AConv (ADCon c indices vs) bs convBnd (ATCon tcon resIndices) -> do
          (xs,template) <- unbind convBnd
          -- indicesTele = Δ
          -- argsTele    = Δ'm
          (_,indicesTele, AConstructorDef _ argsTele) <- lookupDCon c
          b's <- case (template,xs,bs) of
            (AVar x,[x'],[(b,eps)]) | x == x' ->
              pure $ map (\i -> (ANthEq i b,eps)) [1..aTeleLength indicesTele]
            (ATCon tcon' fromIndices,_,_) | tcon == tcon' ->
              -- indices     = As
              -- fromIndices = B's
              -- resIndices  = Bs
              pure $ zipWith3 (\aj b'j bj -> ( AConv (AJoin aj 0 aj 0)
                                                     bs
                                                     (bind xs $ ATyEq aj b'j)
                                                     (ATyEq aj bj)
                                             , Erased ))
                              indices fromIndices resIndices
            _ -> mzero
          v's <- casepush indicesTele resIndices b's
                          vs argsTele
          return $ ACase (ADCon c resIndices v's) bnd ty
        _ -> mzero
  where
    casepush (aTeleNames -> xs) res bs vs0 tele'0 =
      reverse . fst <$> go (reverse vs0) (reverse $ aTeleList tele'0)
      where
        go [] [] = return ([],[])
        go ((v,eps):vs) ((y,e,eps'):tele') | eps == eps' = do
          (v's,ys) <- go vs tele'
          let b's = zipWith (\(vi,epsi) (v'i,_) -> (AJoin vi 0 v'i 0,epsi)) vs v's
              v'  = AConv v
                          (bs ++ b's)
                          (bind (xs ++ ys) e)
                          (substs (zip xs res ++ zip ys (map fst v's)) e)
          return $ ((v',eps) : v's, y : ys)
        go _ _ = mzero
    
    aTeleNames = map (\(y,_,_) -> y) . aTeleList
    
    aTeleList AEmpty = []
    aTeleList (ACons (unrebind -> ((y,  unembed -> e,  eps),  tele'))) =
      (y,e,eps) : aTeleList tele'

astep (ADomEq _) = return Nothing

astep (ARanEq a b) = fmap (ARanEq a) <$> astep b

astep (AAtEq  _) = return Nothing

astep (ANthEq _ _) = return Nothing

astep (ATrustMe _) = return Nothing

astep (ASubstitutedFor a name) = fmap (flip ASubstitutedFor name) <$> astep a
