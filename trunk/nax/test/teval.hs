{-# LANGUAGE GADTs, DataKinds, PolyKinds, KindSignatures, TypeOperators,
	RankNTypes, FlexibleInstances
  #-}

data Ty = N | Ty :-> Ty

data V :: Ty -> * where
  Vfun :: (V a -> V b) -> V (a :-> b)
  Vnat :: Int -> V N

data Lam :: Ty -> * where
  Val :: Int -> Lam N
  App :: Lam (a :-> b) -> Lam a -> Lam b
  Abs :: (V a -> Lam b) -> Lam (a :-> b)

apV :: V (a :-> b) -> V a -> V b
apV (Vfun f) = f

eval :: Lam a -> V a
eval (Val i)     = Vnat i
eval (App e1 e2) = apV (eval e1) (eval e2)
eval (Abs e)     = Vfun (\x -> eval (e x))

{- typed evaluator with other approaches don't work well cause
 - datatyep promotion is still quite limited in current GHC
 -}
