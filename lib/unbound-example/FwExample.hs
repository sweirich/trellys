module FwExample where

import Fw

import Unbound.LocallyNameless
import Data.List

------------------------------------------------------
-- Example terms
------------------------------------------------------

x :: Name Tm
y :: Name Tm
z :: Name Tm
x = string2Name "x"
y = string2Name "y"
z = string2Name "z"

a :: Name Ty
b :: Name Ty
c :: Name Ty
r :: Name Ty
f :: Name Ty
a = string2Name "a"
b = string2Name "b"
c = string2Name "c"
r = string2Name "r"
f = string2Name "f"

_All :: TyName -> Ki -> Ty -> Ty
_All _a _k = All . bind (_a,Embed _k)

_TyLam :: TyName -> Ki -> Ty -> Ty
_TyLam _a _k = TyLam . bind (_a,Embed _k)

_TLam :: TyName -> Ki -> Tm -> Tm
_TLam _a _k = TLam . bind (_a,Embed _k)

_Lam :: TmName -> Ty -> Tm -> Tm
_Lam _x _t = Lam . bind (_x,Embed _t)

-- /\a. \x:a. x
polyid :: Tm
polyid = _TLam a Star (_Lam x (TyVar a) (TmVar x))

-- All a. a -> a
polyidty :: Ty
polyidty = _All a Star (Arr (TyVar a) (TyVar a))

-- \a:*. a
tyid :: Ty
tyid = _TyLam a Star (TyVar a)
-- > runM $ tyid =~ tyid tyid
-- True
-- > runM $ tyid =~ tyid polyidty
-- False

-- Mu and mcata
phiType :: TyName -> TyName -> Ki -> Ty
phiType _f _a k = phiType' _f (TyVar _a) k

phiType' :: TyName -> Ty -> Ki -> Ty
phiType' _f _a k = phiType'' (TyVar _f) _a k

phiType'' :: Ty -> Ty -> Ki -> Ty
phiType'' _f _a k = _All r k $ Arr (_r ==> _a) (TyApp _f _r ==> _a)
 where
 (==>) = hiArr k
 _r = TyVar r

hiArr :: Ki -> Ty -> Ty -> Ty
hiArr k = (==>)
 where
 f1 ==> f2 = foldr (\(i,ki) ty -> _All i ki ty)
                   (foldl TyApp f1 (map TyVar is) `Arr`
                    foldl TyApp f2 (map TyVar is))
                   (zip is (kargs k))
 is = [ string2Name("i"++show n) | n <- [1 .. karity k] ]

mu :: Ki -> Ty
mu k = _TyLam f (KArr k k) $
  foldr (\(i,ki) ty -> _TyLam i ki ty)
        (_All a k (Arr (phiType f a k) (foldl TyApp (TyVar a) (map TyVar is))))
        (zip is (kargs k))
  where
  is = [ string2Name("i"++show n) | n <- [1 .. karity k] ]

kargs :: Ki -> [Ki]
kargs = unfoldr $ \k -> case k of {Star -> Nothing; KArr k1 k2 -> Just (k1,k2)}

karity :: Ki -> Int
karity = length . kargs

{-
*FwExample> runM $ tcty emptyCtx $ mu Star
KArr (KArr Star Star) Star
*FwExample> runM $ tcty emptyCtx $ mu (KArr Star Star)
KArr (KArr (KArr Star Star) (KArr Star Star)) (KArr Star Star)
-}

mitTy :: Ki -> Ty
mitTy k = _All f (KArr k k) $ _All a k $
  Arr (phiType f a k)
      (TyApp (mu k) (TyVar f) ==> TyVar a)
  where (==>) = hiArr k

mit :: Ki -> Tm
mit k = _TLam f (KArr k k) $ _TLam a k $ _Lam x (phiType f a k) $
  foldr (\(i,ki) tm -> _TLam i ki tm)
        (_Lam y mu_f_is $ App (TApp (TmVar y) (TyVar a)) (TmVar x))
        (zip is (kargs k))
  where
  is = [ string2Name("i"++show n) | n <- [1 .. karity k] ]
  mu_f_is = foldl TyApp (mu k) (TyVar f:map TyVar is)

{-
> runM $ ti emptyCtx $ mit Star
All (<(f,{KArr Star Star})> All (<(a1,{Star})> Arr (All (<(r,{Star})> Arr (Arr (TyVar 0@0) (TyVar 1@0)) (Arr (TyApp (TyVar 2@0) (TyVar 0@0)) (TyVar 1@0)))) (Arr (TyApp (TyLam (<(f,{KArr Star Star})> All (<(a,{Star})> Arr (All (<(r,{Star})> Arr (Arr (TyVar 0@0) (TyVar 1@0)) (Arr (TyApp (TyVar 2@0) (TyVar 0@0)) (TyVar 1@0)))) (TyVar 0@0)))) (TyVar 1@0)) (TyVar 0@0))))

> runM $ let k = Star in (mitTy k =~) =<< ti emptyCtx (mit k)
True

> runM $ let k = (KArr Star Star) in (mitTy k =~) =<< ti emptyCtx (mit k)
True
-}

_InTy :: Ki -> Ty
_InTy k = _All f (KArr k k) $
 TyApp (TyVar f) (mu k `TyApp` TyVar f) ==> (mu k `TyApp` TyVar f)
 where (==>) = hiArr k

_In :: Ki -> Tm
_In k = _TLam f (KArr k k) $
  foldr (\(i,ki) tm -> _TLam i ki tm)
        (_Lam x f_mu_k_f_is $
         _TLam a k $
         _Lam y (phiType f a k) $
          tapp_is ( TApp (TmVar y) mu_k_f `App` 
                    (TApp mit_k_f (TyVar a) `App` TmVar y) )
          `App` TmVar x
        )
        (zip is (kargs k))
  where
  is = [ string2Name("i"++show n) | n <- [1 .. karity k] ]
  tapp_is tm = foldl TApp tm (map TyVar is)
  mit_k_f = TApp (mit k) (TyVar f)
  mu_k_f = mu k `TyApp` TyVar f
  f_mu_k_f = TyVar f `TyApp` mu_k_f
  f_mu_k_f_is = foldl TyApp f_mu_k_f (map TyVar is)

