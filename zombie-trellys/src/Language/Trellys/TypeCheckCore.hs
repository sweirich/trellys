-- -*- haskell-program-args: ("-package" "RepLib-0.3.1" "-package" "base-4.3.0.0" "-package" "containers-0.4.0.0" "-package" "directory-1.1.0.0" "-package" "filepath-1.2.0.0" "-package" "mtl-2.0.1.0" "-package" "parsec-3.1.0" "-package" "pretty-1.0.1.2") -*-
-- Note: need to do ":cd ../.." in *haskell* window to make things work.

{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    UndecidableInstances, ViewPatterns, TupleSections #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

module TypeCheckCore where

import Data.List (lookup, find)
import Data.Maybe (isJust)
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Error
import Control.Applicative

import Generics.RepLib hiding (Arrow,Con)
import qualified Generics.RepLib as RL

import Language.Trellys.Error
import Language.Trellys.Environment (Env, err)
import Language.Trellys.GenericBind
import Language.Trellys.Syntax
import Language.Trellys.OpSem (isEValue)

----------------------------------------------------------------
-- Environment stuff, should get folded with the TcM eventually
----------------------------------------------------------------

lookupCoreVar :: (MonadReader Env m, MonadError Err m) => 
                 AName -> m (Theta, ATerm)
lookupCoreVar = undefined

lookupCoreTCon :: (MonadReader Env m, MonadError Err m) => 
                  AName -> m (Integer, ATelescope, Maybe [AConstructorDef])
lookupCoreTCon = undefined 

lookupCoreDCon :: (MonadReader Env m, MonadError Err m) =>
                  AName -> m (AName,      --datatype name
                              ATelescope, --indices
                              ATelescope) --arguments
lookupCoreDCon = undefined

extendCtx :: (MonadReader Env m) =>
          AName -> Theta -> ATerm -> m a -> m a
extendCtx = undefined 

---------------------------------------------------------------
-- Erasing core terms. 
---------------------------------------------------------------
aErase :: (Fresh m, Applicative m) => ATerm -> m ETerm
aErase (AVar x) = return $ EVar (translate x)
aErase (AFO a) = aErase a
aErase (ASquash a) = aErase a
aErase (ACumul a i) = aErase a
aErase (AType i) = return $ EType i
aErase (AUnboxVar th a) = aErase a
aErase (ATCon c indxs) = ECon (translate c) <$> return []
aErase (ADCon c indxs args) = ECon (translate c) <$> mapM (aErase . fst) (filter ((==Runtime) . snd) args)
aErase (AArrow ep bnd) = do
  ((x, unembed -> a), b) <- unbind bnd
  EArrow ep <$> aErase a <*> (bind (translate x) <$> aErase b)
aErase (ALam _ ep bnd) = do
  (x, body) <- unbind bnd
  if ep == Runtime
    then ELam <$> (bind (translate x) <$> aErase body)
    else aErase body
aErase (AApp Runtime a b) = EApp <$> aErase a <*> aErase b
aErase (AApp Erased a b) = aErase a
aErase (AAt a th) = EAt <$> aErase a <*> pure th
aErase (ABoxLL a th) = aErase a
aErase (ABoxLV a) = aErase a
aErase (ABoxP a th) = aErase a
aErase (AAbort _) = return EAbort
aErase (ATyEq a b) = ETyEq <$> aErase a <*> aErase b
aErase (AJoin a i b j) = return EJoin
aErase (AConv a _ _) = aErase a
aErase (AContra a ty) = return EContra
aErase (ASmaller a b) = ESmaller <$> aErase a <*> aErase b
aErase (AOrdAx _ _ _) = return EOrdAx
aErase (AOrdTrans _ _) = return EOrdAx
aErase (AInd _  ep bnd) = do
  ((f, y), r) <- unbind bnd
  if (ep == Runtime) 
   then ERecPlus <$> (bind (translate f, translate y) <$> aErase r)
   else ERecMinus <$> (bind (translate f) <$> aErase r)
aErase (ARec _ ep bnd) = do
  ((f, y), r) <- unbind bnd
  if (ep == Runtime) 
   then ERecPlus <$> (bind (translate f, translate y) <$> aErase r)
   else ERecMinus <$> (bind (translate f) <$> aErase r)
aErase (ALet th ep bnd) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  if ep == Runtime
    then ELet <$> aErase a <*> (bind (translate x) <$> aErase b)
    else aErase b
aErase (ACase a bnd _) = do
  (xeq, matchs) <- unbind bnd
  ECase <$> aErase a <*> (mapM aEraseMatch matchs)

aEraseMatch  :: (Fresh m, Applicative m) => AMatch -> m EMatch
aEraseMatch (AMatch c bnd) = do
  (xeps, b) <- unbind bnd
  EMatch  (translate c)
      <$> (bind (map (translate . fst) $ filter ((==Runtime).snd) xeps) <$> aErase b)


-------------------
-------------------
-- Typechecking!
-------------------
-------------------

coreErr :: (MonadReader Env m, MonadError Err m) => String -> m b
coreErr msg = err [DS $ "Internal error: ill-typed core term. (" ++ msg ++ ")"]

-- Given an environment and a theta, we synthesize a type or fail.
--  Since the synthesized type is "very annotated", this is a bit like regularity.
aTs :: (Fresh m, Applicative m, MonadReader Env m, MonadError Err m) =>  
       Theta -> ATerm -> m ATerm
aTs th (AVar x) = do
  (th', ty) <- lookupCoreVar x
  unless (th == th') $
    coreErr "AVar th"
  return $ ty
aTs Logic   (AFO a) = aTs Program a
aTs Program (ASquash a) = do
 ty <- aErase =<< (aTs Program a)
 case ty of
   (EType _) -> return $ AType 0
   _        -> coreErr "ASquash not type"
aTs th   (ACumul a j) = do
 ty <- aErase =<< (aTs th a)
 case ty of
   (EType i) | i < j -> return $ AType j
   _ -> coreErr "ACumul"
aTs th  (AType i) = return $ AType (i+1)
aTs th' (AUnboxVar th a) = do
  ea <- aErase a
  unless (isJust (isEVar ea)) $
    coreErr "AUnboxVar not var"
  atTy <- aTs th a
  case atTy of
    (AAt ty th'') | th'' == th' -> return ty
                  | otherwise -> coreErr "AUnboxVar th'"
    _  -> coreErr "AUnboxVar not a box"
aTs th (ATCon c idxs) = do
  (i, tys, _) <- lookupCoreTCon c
  aTcTele th (map (,Runtime) idxs) tys
  return (AType i)

aTs th (ADCon c idxs args) = do 
  (tyc, indx_tys, arg_tys) <- lookupCoreDCon c
  aTcTele th (map (,Runtime) idxs ++ args) (indx_tys ++ arg_tys)
  return $ ATCon (translate tyc) (map fst args)

aTs th (AArrow ep bnd) = do
  ((x, unembed -> a), b) <- unbind bnd
  fo <- isEFO =<< (aErase a)
  unless fo $
    coreErr "AArrow FO"
  tya <- aTs th a
  tyb <- extendCtx x th a $ 
           aTs th b
  case (tya, tyb) of
    (AType i, AType 0) -> return $ AType 0
    (AType i, AType j) -> return $ AType (max i j)
    _ -> coreErr "AArrow nontype"

-- Fixme: this is not right, because it assumes the pitype 
-- is AArrow, but we should also accept (AConv (AArrow ...) ...), etc.
aTs th (ALam (AArrow epTy bndTy) ep bnd) = do
  unless (epTy == ep) $
    coreErr "ALam ep"
  aKc th (AArrow epTy bndTy)  
  Just ((x , unembed -> aTy), bTy , _, b) <- unbind2 bndTy bnd
  bTy' <- extendCtx x th aTy $
            aTs th b
  bTyEq <- aeq <$> (aErase bTy) <*> (aErase bTy')
  unless bTyEq $
    coreErr "ALam annotation mismatch"
  return $ (AArrow epTy bndTy)

aTs th (AApp ep a b) = do
  tyA <- aTs th a
  tyB <- aTs th b
  case tyA of
    AArrow ep' bnd -> do
      unless (ep == ep') $
        coreErr "AApp ep mismatch"
      ((x, unembed -> tyB'), tyC) <- unbind bnd
      tyAEq <- aeq <$> aErase tyB <*> aErase tyB'
      unless tyAEq $
        coreErr "AApp dom mismatch"
      return $ subst x b tyC
    _ -> coreErr "AApp not arrow"

aTs th (AAt a th') = do
  aTy <- aTs th' a
  case aTy of 
    AType i -> return $ AType i
    _ -> coreErr "AAt not type"

aTs th (ABoxLL a th') = AAt <$> aTs Logic a <*> pure th'

aTs th (ABoxLV a) = do
  aEVal <- isEValue <$> aErase a
  unless aEVal $
    coreErr "ABoxLV nonvalue"
  AAt <$> aTs Program a <*> pure Program

aTs Program (ABoxP a th') = do
  aTy <- aTs th' a
  return (AAt a th')

aTs Program (AAbort aTy) = do
  aKc Program aTy
  return aTy

aTs th (ATyEq a b) = do
  _ <- aTs Program a
  _ <- aTs Program b
  return (AType 0)

aTs th (AJoin a i b j) = do
 aKc th (ATyEq a b)
 -- joinable <- join a i b j
 let joinable = True --fixme
 unless joinable $
   coreErr "AJoin not joinable"
 return $ ATyEq a b

aTs th (AConv a prfs bnd) = do
  (xs, template) <- unbind bnd
  etemplate <- aErase template
  let runtimeVars = fv etemplate
  aTy <- aTs th a
  unless (length xs == length prfs) $
    coreErr "AConv lenght mismatch"
  eqs <-  let processPrf _ (Runtime,pf) = do
                              pfTy <- aTs Logic pf
                              case pfTy of
                                (ATyEq a1 a2) -> return (a1, a2)
                                _ -> coreErr "AConv not eq"
              processPrf x (Erased,ATyEq a1 a2) = do
                              when (translate x `S.member` runtimeVars) $
                                   coreErr "AConv not erased var"
                              return (a1, a2)
              processPrf _ (Erased, _) = coreErr "AConv malformed irrelevant eq"
           in zipWithM processPrf xs prfs
  let aTy1 = substs (zip xs (map fst eqs)) template
  let aTy2 = substs (zip xs (map snd eqs)) template
  fromEq <- aeq <$> aErase aTy <*> aErase aTy1
  unless fromEq $
    coreErr "AConv wrong type"
  aKc th aTy2
  return aTy2

aTs th (AContra a ty) = do 
  aKc th ty
  aTy <- aTs Logic a
  eaTy <- aErase aTy
  case eaTy of 
    ETyEq (ECon c1 args1) (ECon c2 args2) -> do
      unless (c1 /= c2) $
        coreErr "AContra Not unequal constructors"
      unless (all isEValue args1 && all isEValue args2) $
        coreErr "AContra not values"
      return ty
    _ -> coreErr "AContra not equality"
   
aTs th (ASmaller a b)  = do
  _ <- aTs Program a
  _ <- aTs Program b
  return (AType 0)

aTs th (AOrdAx a a1 a2) = do 
  aTy <- aTs Logic a
  eaTy <- aErase aTy
  ea1 <- aErase a1
  ea2 <- aErase a2
  case eaTy of 
    (ETyEq eb1 (ECon c eb2s)) -> do
       unless (aeq ea2 eb1) $
         coreErr "AOrdAx a2"
       unless (any (aeq ea1) eb2s) $
         coreErr "AOrdAx a1"
       return $ (ASmaller a1 a2)
    _ -> coreErr "AOrdAx badeq"
        
aTs Logic (AOrdTrans a b) = do
  tya <- aTs Logic a
  tyb <- aTs Logic b
  --fixme: this is wrong for the same reason as ALam
  case (tya, tyb) of
    (ASmaller t1 t2, ASmaller t2' t3') | t2 `aeq` t2' ->
       return $ ASmaller t1 t3'
    _ -> coreErr "AOrdTrans"

-- fixme: wrong for same reason as ALam
aTs Logic  (AInd (AArrow epTy bndTy) ep bnd) = do
  unless (epTy == ep) $
    coreErr "AInd ep"
  aKc Logic (AArrow epTy bndTy)
  ((y, unembed -> aTy), bTy) <-unbind bndTy
  ((dumby ,f), dumbb) <- unbind bnd
  let b = subst dumby (AVar y) dumbb
  when (ep == Erased) $ do
    bIsVal <- isEValue <$> aErase b
    unless bIsVal $
      coreErr "AInd Erased nonvalue"
    runtimeVars <- fv <$> aErase b
    when (translate y `S.member` runtimeVars) $
      coreErr "AInd Erased var"
  x <- fresh (string2Name "x")
  z <- fresh (string2Name "z")
  let fTy =  AArrow ep (bind (x, embed aTy)
                       (AArrow Erased (bind (z, embed (ASmaller (AVar x) (AVar y)))
                                            (subst y (AVar x) bTy))))
  bTy' <-
    extendCtx y Logic aTy $
      extendCtx f Logic fTy $
        aTs Logic b
  bTyEq <- aeq <$> aErase bTy <*> aErase bTy'
  unless bTyEq $
    coreErr "AInd annotation mismatch"
  return $ bTy
  
-- fixme: wrong for same reason as ALam
aTs Program  (ARec (AArrow epTy bndTy) ep bnd) = do
  unless (epTy == ep) $
    coreErr "AInd ep"
  aKc Logic (AArrow epTy bndTy)
  ((y, unembed -> aTy), bTy) <-unbind bndTy
  ((dumby ,f), dumbb) <- unbind bnd
  let b = subst dumby (AVar y) dumbb
  when (ep == Erased) $ do
    bIsVal <- isEValue <$> aErase b
    unless bIsVal $
      coreErr "ARec Erased nonvalue"
    runtimeVars <- fv <$> aErase b
    when (translate y `S.member` runtimeVars) $
      coreErr "ARec Erased var"
  bTy' <-
    extendCtx y Logic aTy $
      extendCtx f Logic (AArrow epTy bndTy) $
        aTs Logic b
  bTyEq <- aeq <$> aErase bTy <*> aErase bTy'
  unless bTyEq $
    coreErr "ARec annotation mismatch" 
  return $ bTy
  
aTs th (ALet th' ep bnd) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  when (th' == Program && ep == Erased) $
    coreErr "ALet ep"
  runtimeVars <- fv <$> aErase b
  when (ep == Erased && (translate x) `S.member` runtimeVars) $
    coreErr "ALet erased var"
  aTy <- aTs th' a
  bTy <- extendCtx x th' aTy $ aTs th b
  aKc th bTy
  return bTy

aTs th (ACase a bnd ty) = do
  (xeq, mtchs) <- unbind bnd
  aTy <- aTs th a
  case aTy of 
    (ATCon c idxs) -> do
      tCon <- lookupCoreTCon c
      case tCon of 
        (_, _, Just cons) -> do
          unless (length mtchs == length cons) $
            coreErr "ACase wrong number of branches"
          return $ undefined
        (_, _, Nothing) -> coreErr "ACase case on abstract type"
    _ -> coreErr "ACase not data"
  
{-
  | ACase ATerm (Bind AName [AMatch])
-}

-- Check that a term has a given type
aTc :: (Fresh m, Applicative m, MonadReader Env m, MonadError Err m) => 
           Theta -> ATerm -> ATerm -> m ()
aTc th t ty = do
  ety1 <- aErase =<< (aTs th t)
  ety2 <- aErase ty
  unless (ety1 `aeq` ety2) $
    coreErr "aTC"

-- Check that a term is a type
aKc :: (Fresh m, Applicative m, MonadReader Env m, MonadError Err m) => 
           Theta -> ATerm  -> m ()
aKc th t  = do
  ety <- aErase =<< (aTs th t)
  case ety of
    (EType _) -> return ()
    _ -> coreErr "aKc"


aTcTele :: (Fresh m, Applicative m, MonadReader Env m, MonadError Err m) => 
           Theta -> [(ATerm,Epsilon)] -> ATelescope -> m ()
aTcTele th [] [] = return ()
aTcTele th ((t,ep1):ts) ((x,ty,ep2):tele') = do
  unless (ep1==ep1) $
    coreErr "aTcTele ep"
  aTc th t ty
  aTcTele th ts (subst x t tele')
aTcTele _ _ _ = coreErr "aTcTele telescope length mismatch"

isEFO :: (Fresh m, Applicative m, MonadReader Env m, MonadError Err m) =>
         ETerm -> m Bool
isEFO = undefined

allM :: (Applicative m, Monad m) => (a -> m Bool) -> [a] -> m Bool
allM p xs = and <$> mapM p xs