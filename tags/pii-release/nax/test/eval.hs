{-# LANGUAGE GADTs, DataKinds, PolyKinds, KindSignatures, TypeOperators,
	RankNTypes, FlexibleInstances
  #-}

data V a = Vfun (V a -> V a) | Vinv a -- user should never use Vinv

type Val = V ([String] -> String)

showV :: V ([String] -> String) -> [String] -> String
showV (Vfun f) (x:xs) = "(\\"++x++"."++showV (f (Vinv $ const x)) xs++")"
showV (Vinv g) xs     = g xs

showVal v = showV v $ map return "xyz"++[c:show n | c<-cycle "xyz", n<-[0..]]

instance Show Val where show = showVal

data Nat = Z | S Nat

data Fin :: Nat -> * where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

data Lam :: Nat -> * where
  Var :: Fin n -> Lam n
  App :: Lam n -> Lam n -> Lam n
  Abs :: Lam (S n) -> Lam n

apV (Vfun f) = f

eval :: (Fin n -> Val) -> Lam n -> Val
eval env (Var fn)    = env fn
eval env (App e1 e2) = apV (eval env e1) (eval env e2)
eval env (Abs e)     = Vfun (\x -> eval (ext env x) e)

ext :: (Fin n -> V a) -> V a -> Fin (S n) -> V a
ext env x FZ     = x
ext env x (FS n) = env n

empty :: f Z -> V a
empty _ = error "empty"

