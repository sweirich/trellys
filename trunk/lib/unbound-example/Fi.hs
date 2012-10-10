{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             GADTs #-}
-- copied and modified from unbound 0.3.1 example F.hs extending to Fw and Fi
module Fi where

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
        | KArrI Ty Ki
   deriving Show

data Ty = TyVar TyName
        | Arr Ty Ty
        | All (Bind (TyName, Embed Ki) Ty)
        | AllI (Bind (TmName, Embed Ty) Ty)
        | TyLam (Bind (TyName, Embed Ki) Ty)
        | TyLamI (Bind (TmName, Embed Ty) Ty)
        | TyApp Ty Ty
        | TyAppI Ty Tm
   deriving Show

data Tm = TmVar TmName
        | Lam (Bind (TmName, Embed Ty) Tm)
        | TLam (Bind (TyName, Embed Ki) Tm)
        | TLamI (Bind (TmName, Embed Ty) Tm)
        | App Tm Tm
        | TApp Tm Ty
        | TAppI Tm Tm
   deriving Show

data Delta = Empty
           | ExtTy (Rebind (TyName, Ki) Delta)
           | ExtIx (Rebind (TmName, Ty) Delta)
   deriving Show
type Gamma = [ (TmName, Ty) ]


$(derive [''Ki, ''Ty, ''Tm, ''Delta])

------------------------------------------------------
instance Alpha Ki where
instance Alpha Ty where
instance Alpha Tm where
instance Alpha Delta where

instance Subst Ty Ki where
instance Subst Ty Tm where
instance Subst Ty Delta where
instance Subst Tm Ki where
instance Subst Tm Ty where
instance Subst Tm Delta where
instance Subst Tm Tm where
  isvar (TmVar x) = Just (SubstName x)
  isvar _  = Nothing
instance Subst Ty Ty where
  isvar (TyVar x) = Just (SubstName x)
  isvar _ = Nothing

------------------------------------------------------
-- Example terms
------------------------------------------------------
{-
x :: Name Tm
y :: Name Tm
z :: Name Tm
(x,y,z) = (string2Name "x", string2Name "y", string2Name "z")

a :: Name Ty
b :: Name Ty
c :: Name Ty
(a,b,c) = (string2Name "a", string2Name "b", string2Name "c")

-- /\a. \x:a. x
polyid :: Tm
polyid = TLam (bind (a, Embed Star) (Lam (bind (x, Embed (TyVar a)) (TmVar x))))

-- All a. a -> a
polyidty :: Ty
polyidty = All (bind (a, Embed Star) (Arr (TyVar a) (TyVar a)))

-- \a:*. a
tyid = TyLam (bind (a, Embed Star) (TyVar a))
-- runM $ tyid =~ tyid tyid
-- > True
-- runM $ tyid =~ tyid polyidty
-- > False
-}


-- wrapper for unless over monadic conditions

unlessM mb x = do b <- mb
                  unless b x

-----------------------------------------------------------------
-- beta-eta equivalance/reduction for terms, types, and kinds
-----------------------------------------------------------------

-- beta-eta equivalence on types
t1 =~ t2 | t1 `aeq` t2 = return True
t1 =~ t2 = do
    t1' <- redTy t1
    t2' <- redTy t2
    if t1' `aeq` t1 && t2' `aeq` t2
      then return False
      else t1' =~ t2'

-- beta-eta equivalence on terms
t1 =~~ t2 | t1 `aeq` t2 = return True
t1 =~~ t2 = do
    t1' <- redTm t1
    t2' <- redTm t2
    if t1' `aeq` t1 && t2' `aeq` t2
      then return False
      else t1' =~~ t2'

-- beta-eta equivalence on kinds
k1         =~~~ k2 | k1 `aeq` k2 = return True
KArr k1 k2 =~~~ KArr k1' k2'     = liftM2 (&&) (k1 =~~~ k1') (k2 =~~~ k2')
KArrI t k  =~~~ KArrI t' k'      = liftM2 (&&) (t =~ t') (k =~~~ k')
_          =~~~ _                = return False

-- Parallel beta-eta reduction, prefers beta reductions to eta reductions
redTy (TyVar x) = return (TyVar x)
redTy (Arr t1 t2) = liftM2 Arr (redTy t1) (redTy t2)
redTy (All bnd) = do
   ((x,ek),t) <- unbind bnd
   t' <- redTy t
   return (All (bind (x,ek) t'))
redTy (AllI bnd) = do
   ((x,et),t) <- unbind bnd
   t' <- redTy t
   return (AllI (bind (x,et) t'))
redTy (TyApp t1 t2) = do
  t1' <- redTy t1
  t2' <- redTy t2
  case t1' of
    -- look for a beta-reduction
    TyLam bnd -> do
        ((x,_), t1'') <- unbind bnd
        return $ subst x t2' t1''
    _ -> return $ TyApp t1' t2'
redTy (TyAppI t1 tm) = do
  t1' <- redTy t1
  tm' <- redTm tm
  case t1' of
    -- look for a beta-reduction
    TyLamI bnd -> do
        ((x,_), t1'') <- unbind bnd
        return $ subst x tm' t1''
    _ -> return $ TyAppI t1' tm'
redTy (TyLam bnd) = do
   ((x,ek),t) <- unbind bnd
   t' <- redTy t
   case t of
     -- look for an eta-reduction
     TyApp t1 (TyVar y) | y == x && x `S.notMember` fv t1 -> return t1
     _ -> return (TyLam (bind (x,ek) t'))
redTy (TyLamI bnd) = do
   ((x,et),t) <- unbind bnd
   t' <- redTy t
   case t of
     -- look for an eta-reduction
     TyAppI t1 (TmVar y) | y == x && x `S.notMember` fv t1 -> return t1
     _ -> return (TyLamI (bind (x,et) t'))


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
redTm (TLamI bnd) = do
   ((x,et),tm) <- unbind bnd
   tm' <- redTm tm
   case tm of
     -- look for an eta-reduction
     TAppI tm1 (TmVar y) | y == x && x `S.notMember` fv tm1 -> return tm1
     _ -> return (TLamI (bind (x,et) tm'))
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
redTm (TAppI tm1 tm2) = do
  tm1' <- redTm tm1
  tm2' <- redTm tm2
  case tm1' of
    -- look for a beta-reduction
    TLamI bnd -> do
        ((x,_), tm1'') <- unbind bnd
        return $ subst x tm2' tm1''
    _ -> return $ TAppI tm1' tm2'



-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------

type M = ErrorT String FreshM

runM :: M a -> a
runM m = case (runFreshM (runErrorT m)) of
   Left s  -> error s
   Right a -> a

-- we really need to check |- d but not doing it here TODO
checkTyVar :: Delta -> TyName -> M Ki
checkTyVar d v =
    case d of
      Empty -> throwError ("TyName "++show v++" not found in Delta")
      ExtTy b -> let ((n,k),d') = unrebind b
                  in if n==v then return k else checkTyVar d' v
      ExtIx b -> checkTyVar (snd (unrebind b)) v

lookupTmVar :: TmName -> Delta -> M Ty
lookupTmVar v d =
    case d of
      Empty -> throwError ("TmName "++show v++" not found")
      ExtTy b -> lookupTmVar v (snd (unrebind b))
      ExtIx b -> let ((n,t),d') = unrebind b
                  in if n==v then return t else lookupTmVar v d'

-- we really need to check d |- g but not doing it TODO
lookupCtx :: (Delta,Gamma) -> TmName -> M Ty
lookupCtx (d,g) v =
    case lookup v g of
      Just s -> return s
      Nothing -> lookupTmVar v d

extendTy :: TyName -> Ki -> Delta -> M Delta
extendTy n k d = return $ ExtTy (rebind (n,k) d)

extendIx :: TmName -> Ty -> Delta -> M Delta
extendIx n t d = return $ ExtIx (rebind (n,t) d)

extend :: TmName -> Ty -> Gamma -> Gamma
extend n ty g = (n, ty) : g

tcty :: Delta -> Ty -> M Ki
tcty d  (TyVar x) =
   checkTyVar d x
tcty d  (All b) = do
   ((x,Embed k), ty') <- unbind b
   d' <- extendTy x k d
   tcty d' ty'
tcty d  (AllI b) = do
   ((x,Embed t), ty') <- unbind b
   d' <- extendIx x t d
   tcty d' ty'
tcty d  (Arr t1 t2) = do
   k1 <- tcty d  t1
   unlessM (k1 =~~~ Star) (throwError "KindError")
   k2 <- tcty d  t2
   unlessM (k2 =~~~ Star) (throwError "KindError")
   return Star
tcty d  (TyLam b) = do
   ((x,Embed k), ty') <- unbind b
   d' <- extendTy x k d
   k' <- tcty d' ty'
   return (KArr k k')
tcty d  (TyLamI b) = do
   ((x,Embed t), ty') <- unbind b
   d' <- extendIx x t d
   k' <- tcty d' ty'
   return (KArrI t k')
tcty d  (TyApp t1 t2) = do
   k1 <- tcty d t1
   k2 <- tcty d t2
   case k1 of
     KArr k11 k21 -> do
       unlessM (k2 =~~~ k11) (throwError "KindError")
       return k21
     _ -> throwError "KindError"
tcty d  (TyAppI t1 tm2) = do
   k1 <- tcty d t1
   t2 <- ti (d,[]) tm2
   case k1 of
     KArrI t11 k21 -> do
       unlessM (t2 =~ t11) (throwError "KindError")
       return k21
     _ -> throwError "KindError"

ti :: (Delta,Gamma) -> Tm -> M Ty
ti (d,g) (TmVar x) = lookupCtx (d,g) x
ti (d,g) (Lam bnd) = do
  ((x, Embed ty1), t) <- unbind bnd
  k1 <- tcty d ty1
  unlessM (k1 =~~~ Star) (throwError "KindError")
  ty2 <- ti (d,extend x ty1 g) t
  return (Arr ty1 ty2)
ti g (App t1 t2) = do
  ty1 <- ti g t1
  ty2 <- ti g t2
  case ty1 of
    Arr ty11 ty21 -> do
      unlessM (ty2 =~ ty11) (throwError "TypeError")
      return ty21
    _ -> throwError "TypeError"
ti (d,g) (TLam bnd) = do
  ((x,Embed k), t) <- unbind bnd
  d' <- extendTy x k d
  ty <- ti (d',g) t
  return (All (bind (x,Embed k) ty))
ti (d,g) (TApp t ty) = do
  tyt <- ti (d,g) t
  tyt' <- redTy tyt
  case tyt' of
    All b -> do
      k <- tcty d ty
      ((n1,Embed k'), ty1) <- unbind b
      unlessM (k =~~~ k') (throwError "KindError")
      return $ subst n1 ty ty1
    _ -> throwError "TypeError"
ti (d,g) (TLamI bnd) = do
  ((x,Embed k), t) <- unbind bnd
  d' <- extendIx x k d
  ty <- ti (d',g) t
  return (AllI (bind (x,Embed k) ty))
ti g (TAppI t tm) = do
  tyt <- ti g t
  tyt' <- redTy tyt
  case tyt' of
    AllI b -> do
      ty <- ti g tm
      ((n1,Embed ty'), ty1) <- unbind b
      unlessM (ty =~ ty') (throwError "KindError")
      return $ subst n1 tm ty1
    _ -> throwError "TypeError"

