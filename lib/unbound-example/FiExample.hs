{-# LANGUAGE OverloadedStrings #-}
module FwExample where

import Fi

import Unbound.LocallyNameless
import Data.List

import GHC.Exts( IsString(..) )

-- names as string literals
instance Rep a => IsString (Name a) where
  fromString = string2Name

------------------------------------------------------
-- Example terms
------------------------------------------------------

x,y,z :: Name Tm
x = "x" 
y = "y"
z = "z"

a,b,c,r,f :: Name Ty
a = "a"
b = "b"
c = "c"
r = "r"
f = "f"

emptyCtx = (Empty,[])

_All :: TyName -> Ki -> Ty -> Ty
_All _a _k = All . bind (_a,Embed _k)

_AllI :: TmName -> Ty -> Ty -> Ty
_AllI _a _t = AllI . bind (_a,Embed _t)

_TyLam :: TyName -> Ki -> Ty -> Ty
_TyLam _a _k = TyLam . bind (_a,Embed _k)

_TyLamI :: TmName -> Ty -> Ty -> Ty
_TyLamI _a _t = TyLamI . bind (_a,Embed _t)

_TLam :: TyName -> Ki -> Tm -> Tm
_TLam _a _k = TLam . bind (_a,Embed _k)

_TLamI :: TmName -> Ty -> Tm -> Tm
_TLamI _a _t = TLamI . bind (_a,Embed _t)

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
-- > runM $ tyid =~ TyApp tyid tyid
-- True
-- > runM $ tyid =~ TyApp tyid polyidty
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
 f1 ==> f2 = foldr (\(i,tk) ty -> case tk of
                                   Right k -> _All (string2Name i) k ty
                                   Left t -> _AllI (string2Name i) t ty)
                   (foldl tyApp f1 is' `Arr` foldl tyApp f2 is')
                   is'
 is' = zip is (kargs k)
 is = [ "i"++show n | n <- [1 .. karity k] ]

tyApp ty (i,Right _) = TyApp ty (TyVar $ string2Name i) 
tyApp ty (i,Left _) = TyAppI ty (TmVar $ string2Name i)

mu :: Ki -> Ty
mu k = _TyLam f (KArr k k) $
  foldr (\(i,tk) ty -> case tk of
                         Right k -> _TyLam (string2Name i) k ty
                         Left t -> _TyLamI (string2Name i) t ty)
        (_All a k (Arr (phiType f a k) (foldl tyApp (TyVar a) is')))
        is'
  where
  is' = zip is (kargs k)
  is = [ "i"++show n | n <- [1 .. karity k] ]

kargs :: Ki -> [Either Ty Ki]
kargs = unfoldr $ \k -> case k of Star -> Nothing
                                  KArr k1 k2 -> Just (Right k1,k2)
                                  KArrI t1 k2 -> Just (Left t1,k2)

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
  foldr (\(i,tk) tm -> case tk of
                         Right ki -> _TLam (string2Name i) ki tm
                         Left ty -> _TLamI (string2Name i) ty tm)
        (_Lam y mu_f_is $ App (TApp (TmVar y) (TyVar a)) (TmVar x))
        is'
  where
  is' = zip is (kargs k)
  is = [ "i"++show n | n <- [1 .. karity k] ]
  mu_f_is = foldl tyApp (mu k) ((name2String f,Right undefined):is')

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
  foldr (\(i,tk) tm -> case tk of
                         Right ki -> _TLam (string2Name i) ki tm
                         Left ty -> _TLamI (string2Name i) ty tm)
        (_Lam x f_mu_k_f_is $
         _TLam a k $
         _Lam y (phiType f a k) $
          tapp_is ( TApp (TmVar y) mu_k_f `App` 
                    (TApp mit_k_f (TyVar a) `App` TmVar y) )
          `App` TmVar x
        )
        is'
  where
  is' = zip is (kargs k)
  is = [ "i"++show n | n <- [1 .. karity k] ]
  tapp_is tm = foldl tApp tm is'
  mit_k_f = TApp (mit k) (TyVar f)
  mu_k_f = mu k `TyApp` TyVar f
  f_mu_k_f = TyVar f `TyApp` mu_k_f
  f_mu_k_f_is = foldl tyApp f_mu_k_f is'

tApp tm (i,Right _) = TApp tm (TyVar $ string2Name i)
tApp tm (i,Left _) = TAppI tm (TmVar $ string2Name i)

{-
> runM $ let k = KArr Star Star in (_InTy k =~) =<< ti emptyCtx (_In k)
True
 -}
