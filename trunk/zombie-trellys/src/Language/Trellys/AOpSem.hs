{-# LANGUAGE ViewPatterns, TupleSections #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.AOpSem
  ( isPlainAValue, isConvAValue
  , Correspondence(..), correspondingVarName, symEq, composeEq, disunify
  , astep, asteps)
where

import Language.Trellys.Syntax
import Language.Trellys.Environment (lookupDCon, lookupDef)
import Language.Trellys.TypeMonad
import Language.Trellys.GenericBind
import Language.Trellys.TypeCheckCore
import Language.Trellys.OpSem

--Stuff used for debugging.
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ ( (<>), (<+>),hsep,text, parens, brackets, nest, render)

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
  return . AConv (AJoin a 0 a 0 CBV) [(pab,Runtime)] (bind [x] $ ATyEq (AVar x) a) $ ATyEq b a

-- composeEq A C (pAB : A = B) (pBC : B = C) : A = C
composeEq :: Fresh m => ATerm -> ATerm -> ATerm -> ATerm -> m ATerm
composeEq a c pab pbc = do
  x <- fresh $ string2Name "x"
  return . AConv pab [(pbc,Runtime)] (bind [x] . ATyEq a $ AVar x) $ ATyEq a c

unbind2M :: (MonadPlus m, Fresh m, Alpha p1, Alpha p2, Alpha t1, Alpha t2)
         => GenBind order card p1 t1
         -> GenBind order card p2 t2
         -> m (p1, t1, p2, t2)
unbind2M bnd bnd' = maybe mzero return =<< unbind2 bnd bnd'

-- lunbind2M :: (MonadPlus m, LFresh m, Alpha p1, Alpha p2, Alpha t1, Alpha t2)
--          => GenBind order card p1 t1
--          -> GenBind order card p2 t2
--          -> ((p1, t1, p2, t2) -> m r) -> m r
-- lunbind2M bnd bnd' k =          
--   lunbind2 bnd bnd' $ maybe mzero k 

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
    
    go (ADCon d th as bs) (ADCon d' th' as' bs')
      | th == th' && d == d' && length as == length as' && length bs == length bs' =
        ADCon d th <$> zipWithM go as as'
                   <*> zipWithM (\(b,eps) (b',eps') -> do
                                 guard $ eps == eps'
                                 b'' <- go b b'
                                 pure (b'',eps))
                             bs bs'

    go (AArrow th ex eps bnd) (AArrow th' _ eps' bnd') | th == th' && eps == eps' = do
      ((x, unembed -> dom), ran, (_, unembed -> dom'), ran') <- unbind2M bnd bnd'
      dom'' <- go dom dom'
      ran'' <- go ran ran'
      pure . AArrow th ex eps $ bind (x, embed dom'') ran''
    
    go (ALam th ty eps bnd) (ALam th' ty' eps' bnd') | th == th' && eps == eps' = do
      (x,body,_,body') <- unbind2M bnd bnd'
      ty''             <- go ty ty'
      body''           <- go body body'
      pure . ALam th ty'' eps $ bind x body''
    
    go (AApp eps a b t) (AApp eps' a' b' t') | eps == eps' =
      AApp eps <$> go a a' <*> go b b' <*> go t t'
    
    go (AAt a th) (AAt a' th') | th == th' =
      AAt <$> go a a' <*> pure th
    
    go (AUnbox a) (AUnbox a') =
      AUnbox <$> go a a'
    
    go (ABox a th) (ABox a' th') | th == th' =
      ABox <$> go a a' <*> pure th
    
    go (AAbort a) (AAbort a') =
      AAbort <$> go a a'
    
    go (ATyEq a b) (ATyEq a' b') =
      ATyEq <$> go a a' <*> go b b'
    
    go (AJoin a i b j strategy) (AJoin a' i' b' j' strategy') | i == i' && j == j' =
      AJoin <$> go a a' <*> pure i <*> go b b' <*> pure j <*> pure strategy
    
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
    
    go (ALet eps bnd (th,ty)) (ALet eps' bnd' (th',ty')) 
        | eps == eps' && th == th' = do
      ((x, y, unembed -> a), b, (_, _, unembed -> a'), b') <- unbind2M bnd bnd'
      a'' <- go a a'
      b'' <- go b b'
      ty'' <- go ty ty'
      pure (ALet eps (bind (x, y, embed a'') b'') (th, ty''))
     
    go (ACase a bnd (th,ty)) (ACase a' bnd' (th',ty')) | th == th' = do
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
          -- it's not necessary---unrebind doesn't freshen variable names
          -- if you want them to use the same names you need to use
          -- unbind2 on teleBnd and teleBnd'
          goTele (ACons (unrebind -> ((y,  unembed -> b,  eps),  teleTail )))
                 (ACons (unrebind -> ((y', unembed -> b', eps'), teleTail')))
            | eps == eps' = do
              b''        <- go b b'
              teleTail'' <- goTele teleTail $ subst y (AVar y') teleTail'
              pure . ACons $ rebind (y, embed b'', eps) teleTail''
          goTele _ _ =
            mzero
      arms'' <- zipWithM goMatch arms arms'
      ty''   <- go ty ty'
      ACase <$> go a a'
            <*> pure (bind x arms'')
            <*> pure (th, ty'')
    
    go (ADomEq a) (ADomEq a') =
      ADomEq <$> go a a'
    
    go (ARanEq p a b) (ARanEq p' a' b') =
      ARanEq <$> go p p' <*> go a a' <*> go b b'
    
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
  --liftIO . putStrLn $ "considering the application" ++ render (disp (AApp eps a b ty))
  stepA <- astep a
  case stepA of
    Just (AAbort t) -> return . Just $ AAbort t
    Just a'         -> return . Just $ AApp eps a' b ty
    Nothing         -> do
      aval <- isConvAValue a
      if not aval
        then do 
          --liftIO . putStrLn $ render (disp a) ++ " , the a, is not a conv-value, so there!"
          return Nothing
        else do
          stepB <- astep b
          case stepB of
            Just (AAbort t) -> return . Just $ AAbort t
            Just b'         -> return . Just $ AApp eps a b' ty
            Nothing         -> do
              --liftIO . putStrLn $ "Neither a nor b steps."
              bval <- isConvAValue b
              if not bval
                then do
                    --liftIO . putStrLn $ render (disp b) ++ " is not a conv-value, so there!"
                    return Nothing
                else case a of
                  -- If a is a converted value we have to do something smart.
                  AConv funv bs convBnd toTy@(eraseToHead->AArrow resTh resEx resEps resTyBnd) -> do
                    (xs,template) <- unbind convBnd
                    case (template,xs,bs) of                      
                      (AVar x,[xx],[(p,Runtime)]) | x == xx -> do
                        (_, ATyEq (AArrow si srcEx  srcEps  srcTyBnd)
                                  (AArrow ri resEx' resEps' resTyBnd')) <- aTs p
                        guard $ si == ri                                           
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
                        let convInput :: ATerm -> ATerm
                            convInput v =       AConv v
                                                      [(ADomEq p, Runtime)]
                                                      (bind [x'] $ AVar x')
                                                      srcDom
                        let convOutput :: ATerm {- the input value -}
                                          -> ATerm {- the body -}
                                          -> ATerm
                            convOutput v body = AConv body
                                                      [(ARanEq p (convInput v) v, Runtime)]
                                                      (bind [x'] $ AVar x')
                                                      (subst tyVar v resRan)
                        runMaybeT $ 
                          convOutput b <$> stepFun funv (convInput b)
                      (AArrow srcTh srcEx srcEps srcTyBnd,_,_) -> do
                        ( (tyVar, unembed -> srcDom), srcRan,
                          (_,     unembed -> resDom), resRan ) <- unbind2M srcTyBnd resTyBnd
                        froms   <- mapM (\pf_ep ->
                                             case pf_ep of                                               
                                               (ATyEq ty1 ty2, Erased) -> 
                                                  return ty1
                                               (_ , Erased) -> error "astep: malformed erased proof, not an eq"
                                               (pf , Runtime) -> do
                                                  (Logic, ATyEq ty1 ty2) <- getType pf
                                                  return ty1)
                                        bs
                        symm_bs <- mapM (\pf_ep ->
                                             case pf_ep of
                                               (ATyEq ty1 ty2, Erased) -> 
                                                  return (ATyEq ty2 ty1, Erased)
                                               (_ , Erased) -> error "astep: malformed erased proof, not an eq"
                                               (pf , Runtime) -> do
                                                  (Logic, ATyEq ty1 ty2) <- getType pf
                                                  symmPf <- symEq ty1 ty2 pf
                                                  return (symmPf, Runtime))
                                        bs
                        let convInput :: ATerm -> ATerm
                            convInput v =  AConv v
                                                 symm_bs
                                                 (bind xs srcDom)
                                                 (substs (zip xs froms) srcDom)
                        let convOutput :: ATerm {- the input -}
                                          -> ATerm {- the body -}
                                          -> ATerm
                            convOutput v body = AConv body
                                                      (bs ++ [(AJoin (convInput v) 0 v 0 CBV,Runtime)])
                                                      (bind (xs++[tyVar]) $ srcRan)
                                                      (subst tyVar v resRan)
                        runMaybeT $
                          convOutput b <$> stepFun funv (convInput b)
                      _ ->  do
                              --liftIO . putStrLn $ "somehow we ended up in the 'other' case?"
                              mzero
                  -- Otherwise, if a is not a converted value, it is either a function value or the 
                  -- application is stuck, so we let stepFun do its thing.
                  _ -> do
                         --liftIO . putStrLn $ "None of the conv cases triggered"
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
      AConv (ABox v th) bs convBnd (AAt tyRes th') | th == th' -> do
        (xs,template) <- unbind convBnd
        case (template,xs,bs) of
          (AVar x,[x'],[(b,eps)]) | x == x' -> do
            y <- fresh $ string2Name "y"
            return . Just
                   . AUnbox
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

astep (AJoin _ _ _ _ _) = return Nothing

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
        AConv (ADCon c th indices vs) bs convBnd (eraseToHead-> ATCon tcon resIndices) -> do
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
              pure $ zipWith3 (\aj b'j bj -> ( AConv (AJoin aj 0 aj 0 CBV)
                                                     bs
                                                     (bind xs $ ATyEq aj b'j)
                                                     (ATyEq aj bj)
                                             , Erased ))
                              indices fromIndices resIndices
            _ -> mzero
          v's <- casepush indicesTele resIndices b's
                          vs argsTele
          return $ ACase (ADCon c th resIndices v's) bnd ty
        _ -> mzero
  where
    casepush (aTeleNames -> xs) res bs vs0 tele'0 =
      reverse . fst <$> go (reverse vs0) (reverse $ aTeleList tele'0)
      where
        go [] [] = return ([],[])
        go ((v,eps):vs) ((y,e,eps'):tele') | eps == eps' = do
          (v's,ys) <- go vs tele'
          let b's = zipWith (\(vi,epsi) (v'i,_) -> (AJoin vi 0 v'i 0 CBV,epsi)) vs v's
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

astep (ARanEq p a a') = return Nothing

astep (AAtEq  _) = return Nothing

astep (ANthEq _ _) = return Nothing

astep (ATrustMe _) = return Nothing

astep (ASubstitutedFor a _) = return $ Just a


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

