{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             GADTs,
             CPP #-}
-- copied and modified from unbound 0.3.1 example F.hs extending to Fw
module Fw where

import Unbound.LocallyNameless

import Control.Monad
import Control.Monad.Trans.Error
-- import Data.List as List
import Data.Set as S

-- System Fw with type and term variables

type TyName = Name Ty
type TmName = Name Tm

data Ki = Star
        | KArr Ki Ki
   deriving Show

data Ty = TyVar TyName
        | Arr Ty Ty
        | All (Bind (TyName, Embed Ki) Ty)
        | TyLam (Bind (TyName, Embed Ki) Ty)
        | TyApp Ty Ty
   deriving Show

data Tm = TmVar TmName
        | Lam (Bind (TmName, Embed Ty) Tm)
        | TLam (Bind (TyName, Embed Ki) Tm)
        | App Tm Tm
        | TApp Tm Ty
   deriving Show

$(derive [''Ki, ''Ty, ''Tm])

------------------------------------------------------
instance Alpha Ki where
instance Alpha Ty where
instance Alpha Tm where

instance Subst Ty Ki where
instance Subst Ty Tm where
instance Subst Tm Ki where
instance Subst Tm Ty where
instance Subst Tm Tm where
  isvar (TmVar x) = Just (SubstName x)
  isvar _  = Nothing
instance Subst Ty Ty where
  isvar (TyVar x) = Just (SubstName x)
  isvar _ = Nothing

-----------------------------------------------------------------
-- beta-eta equivalance/reduction for types
-----------------------------------------------------------------

-- beta-eta equivalence
t1 =~ t2 | t1 `aeq` t2 = return True
t1 =~ t2 = do
    t1' <- redTy t1
    t2' <- redTy t2
    if t1' `aeq` t1 && t2' `aeq` t2
      then return False
      else t1' =~ t2'

-- Parallel beta-eta reduction, prefers beta reductions to
-- eta reductions
redTy (TyVar x) = return (TyVar x)
redTy (Arr t1 t2) = liftM2 Arr (redTy t1) (redTy t2)
redTy (All bnd) = do
   ((x,ek),t) <- unbind bnd
   t' <- redTy t
   return (All (bind (x,ek) t'))
redTy (TyApp t1 t2) = do
  t1' <- redTy t1
  t2' <- redTy t2
  case t1' of
    -- look for a beta-reduction
    TyLam bnd -> do
        ((x,_), t1'') <- unbind bnd
        return $ subst x t2' t1''
    _ -> return $ TyApp t1' t2'
redTy (TyLam bnd) = do
   ((x,ek),t) <- unbind bnd
   t' <- redTy t
   case t of
     -- look for an eta-reduction
     TyApp t1 (TyVar y) | y == x && x `S.notMember` fv t1 -> return t1
     _ -> return (TyLam (bind (x,ek) t'))



-- Parallel beta-eta reduction, prefers beta reductions to
-- eta reductions
redTm (TmVar x) = return (TmVar x)
redTm (Lam bnd) = do
   ((x,et),tm) <- unbind bnd
   tm' <- redTm tm
   case tm of
     -- look for an eta-reduction
     App tm1 (TmVar y) | y == x && x `S.notMember` fv tm1 -> return tm1
     _ -> return (Lam (bind (x,et) tm'))
redTm (TLam bnd) = do
   ((x,ek),tm) <- unbind bnd
   tm' <- redTm tm
   case tm of
     -- look for an eta-reduction
     TApp tm1 (TyVar y) | y == x && x `S.notMember` fv tm1 -> return tm1
     _ -> return (TLam (bind (x,ek) tm'))
redTm (App tm1 tm2) = do
  tm1' <- redTm tm1
  tm2' <- redTm tm2
  case tm1' of
    -- look for a beta-reduction
    Lam bnd -> do
        ((x,_), tm1'') <- unbind bnd
        return $ subst x tm2' tm1''
    _ -> return $ App tm1' tm2'
redTm (TApp tm1 ty2) = do
  tm1' <- redTm tm1
  ty2' <- redTy ty2
  case tm1' of
    -- look for a beta-reduction
    TLam bnd -> do
        ((x,_), tm1'') <- unbind bnd
        return $ subst x ty2' tm1''
    _ -> return $ TApp tm1' ty2'


-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------
type Delta = [ (TyName, Ki) ]
type Gamma = [ (TmName, Ty) ]

data Ctx = Ctx { getDelta :: Delta , getGamma :: Gamma }
emptyCtx = Ctx { getDelta = [], getGamma = [] }

type M = ErrorT String FreshM

runM :: M a -> a
runM m = case (runFreshM (runErrorT m)) of
   Left s  -> error s
   Right a -> a

checkTyVar :: Ctx -> TyName -> M Ki
checkTyVar g v = do
    case lookup v (getDelta g) of
      Just k -> return k
      Nothing -> throwError ("NotFound "++show v)

lookupTmVar :: Ctx -> TmName -> M Ty
lookupTmVar g v = do
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwError ("NotFound "++show v)

extendTy :: TyName -> Ki -> Ctx -> Ctx
extendTy n k ctx = ctx { getDelta =  (n, k) : (getDelta ctx) }

extendTm :: TmName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : (getGamma ctx) }

tcty :: Ctx -> Ty -> M Ki
tcty g  (TyVar x) =
   checkTyVar g x
tcty g  (All b) = do
   ((x,Embed k), ty') <- unbind b
   tcty (extendTy x k g) ty'
tcty g  (Arr t1 t2) = do
   k1 <- tcty g  t1
   unless (k1 `aeq` Star) (throwError "KindError")
   k2 <- tcty g  t2
   unless (k2 `aeq` Star) (throwError "KindError")
   return Star
tcty g  (TyLam b) = do
   ((x,Embed k), ty') <- unbind b
   k' <- tcty (extendTy x k g) ty'
   return (KArr k k')
tcty g  (TyApp t1 t2) = do
   k1 <- tcty g t1
   k2 <- tcty g t2
   case k1 of
     KArr k11 k21 | k2 `aeq` k11 ->
       return k21
     _ -> throwError "KindError"

ti :: Ctx -> Tm -> M Ty
ti g (TmVar x) = lookupTmVar g x
ti g (Lam bnd) = do
  ((x, Embed ty1), t) <- unbind bnd
  k1 <- tcty g ty1
  unless (k1 `aeq` Star) (throwError "KindError")
  ty2 <- ti (extendTm x ty1 g) t
  return (Arr ty1 ty2)
ti g (App t1 t2) = do
  ty1 <- ti g t1
  ty2 <- ti g t2
  ty1' <- redTy ty1
  ty2' <- redTy ty2
  case ty1' of
    Arr ty11 ty21 -> do
      b <- ty2 =~ ty11
      unless b (throwError $ "TypeError:"++__FILE__++":"++show __LINE__++":"
                           ++"expected the following type to be equal\n"
                           ++show ty2'++"\n"++show ty11
                           ++"\n"++show ty1'
                           ++"\n"++show ty2'
               )
      return ty21
    _ -> throwError $ "TypeError:"++__FILE__++":"++show __LINE__++":"
                    ++"expected Arr but "++show ty1
ti g (TLam bnd) = do
  ((x,Embed k), t) <- unbind bnd
  ty <- ti (extendTy x k g) t
  return (All (bind (x,Embed k) ty))
ti g (TApp t ty) = do
  tyt <- ti g t
  tyt' <- redTy tyt
  case tyt' of
    All b -> do
      k <- tcty g ty
      ((n1,Embed k'), ty1) <- unbind b
      unless (k `aeq` k') (throwError "KindError")
      return $ subst n1 ty ty1
    _ -> throwError $ "TypeError:"++__FILE__++":"++show __LINE__++":"
                    ++"expected All but "++show tyt'

