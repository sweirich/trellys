
{-# LANGUAGE GADTs
  , RankNTypes
  , ImpredicativeTypes
  , FlexibleInstances
  , ScopedTypeVariables #-}

data E r where
  EInt :: Int -> E r 
  EApp :: r -> r -> E r
  EAbs :: (r -> r) -> E r
  EPair:: r -> r -> E r
  E1:: r -> E r
  E2:: r -> E r

eint n = In (EInt n)
eapp f x = In (EApp f x)
eabs f = In (EAbs f)
epair x y = In(EPair x y)
e1 x = In(E1 x)
e2 x = In(E2 x)

type Exp = (forall a . Fix E a)
type Value = (forall a . Fix V a)
type Nat = (forall a . Fix N a)

data N r where
  Z :: N r
  S :: r -> N r
  
data V r where
  VInt :: Int -> V r
  VAbs :: (r -> r) -> V r
  VPair :: r -> r -> V r

-- Fix point operator for HOAS

data Fix f a = In (f (Fix f a)) | Inv a

-- Fix point operator for First order data

data Fix0 f = In0 f (Fix0 f)

------------------------------------------------------------
type Phi f a = (forall r . (r a -> a) -> (a -> r a) -> f (r a) -> a) 

msfcata2 :: Phi f a -> Fix f a -> a
msfcata2 phi (In x) = phi (msfcata2 phi) Inv x 
msfcata2 phi (Inv x) = x

msfcata :: Phi f a -> (forall a . Fix f a) -> a
msfcata phi x = msfcata2 phi x


-----------------------------------------------------
-- some example terms

qq = eabs(\ f -> eabs (\ x -> eapp f x))
zz = eapp (eapp qq (eabs (\ x -> x))) (eint 6)              
z2 = eapp (eapp qq (eabs (\ x -> e1 x))) (epair (eint 33) (eint 7))


eval:: Exp -> Value
eval x = msfcata phi x
  where phi :: Phi E (Fix V b)
        phi rcall inv (EInt n) = In(VInt n)
        phi rcall inv (EAbs f) = In (VAbs(rcall . f . inv))
        phi rcall inv (EPair x y) = In(VPair (rcall x) (rcall y))
        phi rcall inv (E1 x) = proj(rcall x)
          where proj (In(VPair u v)) = u
        phi rcall inv (E2 x) = proj(rcall x)
          where proj (In(VPair u v)) = v          
        phi rcall inv (EApp f x) = apply (rcall f) (rcall x)
          where apply (In(VAbs f)) x = f x
        
reify:: Value -> Exp
reify x = msfcata phi x
  where phi:: Phi V (Fix E b)
        phi rcall inv (VInt n) = In(EInt n)
        phi rcall inv (VAbs f) = In(EAbs(rcall . f . inv))
        phi rcall inv (VPair x y) = In(EPair (rcall x) (rcall y))

norm :: Exp -> Exp
norm x = reify (eval x) 

plus1:: Exp -> Exp
plus1 x = msfcata phi x
  where phi:: Phi E (Fix E b)
        phi rcall inv (EInt n) = In(EInt (n+1))
        phi rcall inv (EApp f x) = In(EApp (rcall f) (rcall x))
        phi rcall inv (EAbs f) = In(EAbs(rcall . f . inv))
        phi rcall inv (EPair y x) = In(EPair (rcall y) (rcall x))
        phi rcall inv (E1 x) = In(E1 (rcall x))
        phi rcall inv (E2 x) = In(E2 (rcall x))
        
showE:: Exp -> Int -> String
showE x = msfcata phi x
  where phi :: Phi E (Int -> String)
        phi rcall inv (EInt n) = const (show n)
        phi rcall inv (EApp f x) = \ n -> concat["(",rcall f n," ",rcall x n,")"]
        phi rcall inv (EPair y x) = \ n -> concat["(",rcall y n,",",rcall x n,")"] 
        phi rcall inv (E1 x) = \ n ->  concat["(Pr1 ",rcall x n,")"] 
        phi rcall inv (E2 x) = \ n ->  concat["(Pr2 ",rcall x n,")"] 
        phi rcall inv (EAbs f) = g
          where g n = concat["(\\ ",new n," -> ",rcall (f (inv (const (new n)))) (n+1),")"]
                new n = "x"++show n
                
pp :: Exp -> IO ()                
pp x = putStrLn(showE x 1)   

---------------------------------------------------------
-- attempts at a useable primitive recursion, not too hopeful

msfprim2 :: (forall r  . (r a -> a) -> 
                         (a -> r a) -> 
                         (r a -> (a -> Fix f a) -> Fix f a) -> 
                         (f (r a) -> a)) -> 
            Fix f a -> a
msfprim2 phi (In x) = phi (msfprim2 phi) Inv (\ x f -> lift f x) x 
msfprim2 phi (Inv x) = x

msfprim :: (forall r .  (r a -> a) -> 
                        (a -> r a) -> 
                        (r a -> (a -> Fix f a) -> Fix f a) -> 
                        (f (r a) -> a)) -> 
            (forall a . Fix f a) -> a
msfprim phi x = msfprim2 phi x

lift f (Inv x) = f x
lift f x = x

out:: (forall a . Fix f a) -> (forall a . f (Fix f a))
out (In x) = x

                            
          