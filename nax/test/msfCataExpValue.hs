
{-# LANGUAGE GADTs
  , RankNTypes
  , ImpredicativeTypes
  , FlexibleInstances
  , ScopedTypeVariables
  , KindSignatures
  , MultiParamTypeClasses
  , TypeFamilies  #-}


data N r where
  Z :: N r
  S :: r -> N r

data L a r where
  Nil:: L a r
  Cons:: a -> r -> L a r
  
data Tr r = Tip Int | Fork r r

data E r where
  EInt :: Int -> E r 
  EApp :: r -> r -> E r
  EAbs :: (r -> r) -> E r
  EPair:: r -> r -> E r
  E1:: r -> E r
  E2:: r -> E r

eint n    = In (EInt n)
eapp f x  = In (EApp f x)
eabs f    = In (EAbs f)
epair x y = In (EPair x y)
e1 x      = In (E1 x)
e2 x      = In (E2 x)

type Exp = (forall a . Fix E a)
type Value = (forall a . Fix V a)
type Nat = (forall a . Fix N a)

data V r where
  VInt :: Int -> V r
  VAbs :: (r -> r) -> V r
  VPair :: r -> r -> V r


--------------------------------------------------
-- Simple non-indexed, First-order data

data Fix0 f = In0 (f (Fix0 f))

--                  rcall       data   answer
mcata:: (forall r . (r -> a) -> f r -> a) -> 
        (Fix0 f -> a)
mcata phi (In0 x) = phi (mcata phi) x




type Lex f g = (forall r s. (r -> Fix0 g) -> 
                            (s -> Fix0 g -> Fix0 g) ->
                            (f s) ->
                            (g r) -> 
                            Fix0 g)

lexcata:: Lex f g -> Fix0 f -> Fix0 g -> Fix0 g  
lexcata phi (In0 x) (In0 y) = phi (lexcata phi (In0 x))
                                  (lexcata phi)
                                  x y
                                  
ack n m = lexcata phi n m
  where phi:: Lex N N
        phi inner outer _ Z = zero
        phi inner outer Z (S m) = suc (inner m)
        phi inner outer (S n) (S m) = outer n (inner m)
        

zero = In0 Z
suc n = In0(S n)
one = suc zero 

nil = In0 Nil
cons x y = In0 (Cons x y)

tip x = In0(Tip x)
fork x y = In0(Fork x y)


len:: Fix0 (L a) -> Int
len x = mcata phi x
  where phi:: (r -> Int) -> L a r -> Int
        phi r Nil = 0
        phi r (Cons x xs) = 1 + r xs



mprim::    
  (forall r . (r -> a) -> 
              (r -> Fix0 f) -> 
              (f r ->  a)) ->
  (Fix0 f -> a)
mprim phi (In0 x) = phi (mprim phi) id x 

mult :: Fix0 N -> Fix0 N -> Fix0 N
mult x y = undefined
add:: Fix0 N -> Fix0 N -> Fix0 N
add x y = undefined




fact n = mprim phi n
  where phi:: (r -> Fix0 N) -> 
              (r -> Fix0 N) -> 
              (N r -> Fix0 N)
        phi r cast Z = In0 Z
        phi r cast (S n) = mult (suc (cast n)) (r n)

mcvr::    
  (forall r . (r -> a) -> 
              (r -> f r) -> 
              (f r ->  a)) ->
  (Fix0 f -> a)
mcvr phi (In0 x) = phi (mcvr phi) unIn x 
  where unIn (In0 x) = x


fib n = mcvr phi n 
  where phi:: (r -> Fix0 N) -> 
              (r -> N r) -> 
              (N r ->  Fix0 N)
        phi r pred Z = one
        phi r pred (S n) = 
          case pred n of
            Z -> one
            (S m) -> add (r n) (r m)


------------------------------------
-- mu[k] F
-- mu[k,t] F
-- Fix point operator for HOAS

data Fix f a = In (f (Fix f a)) | Inv a

-- Fix point operator for First order data


-- lexcata:: 


------------------------------------------------------------
type Phi f a = (forall r . (r a -> a) -> (a -> r a) -> f (r a) -> a) 


msfcata2 :: Phi f a -> Fix f a -> a
msfcata2 phi (In x) = phi (msfcata2 phi) Inv x 
msfcata2 phi (Inv x) = x

msfcata :: Phi f a -> (forall a . Fix f a) -> a
msfcata phi x = help phi x
  where help :: Phi f a -> Fix f a -> a
        help phi (In x) = phi (help phi) Inv x 
        help phi (Inv x) = x



-----------------------------------------------------
-- some example terms

-- \ f -> \ x -> f x
qq = eabs(\ f -> eabs (\ x -> eapp f x))
-- (\ f -> \ x -> f x) (\ x -> x) 6
zz = eapp (eapp qq (eabs (\ x -> x))) (eint 6) 
-- (\ f -> \ x -> f x) (\ x -> fst x) (33,7)
z2 = eapp (eapp qq (eabs (\ x -> e1 x))) (epair (eint 33) (eint 7))

c1 = putStrLn(showE qq 0)
c2 = putStrLn(showE zz 33)
c3 = putStrLn(showE z2 0)

showE:: Exp -> Int -> String
showE x = msfcata phi x  where 
  phi :: Phi E (Int -> String)
  phi rcall inv (EInt i) n = (show i)
  phi rcall inv (EApp f x) n = concat["(",rcall f n," ",rcall x n,")"]
  phi rcall inv (EPair y x) n = concat["(",rcall y n,",",rcall x n,")"] 
  phi rcall inv (E1 x) n = concat["(fst ",rcall x n,")"] 
  phi rcall inv (E2 x) n = concat["(snd ",rcall x n,")"] 
  phi rcall inv (EAbs f) n = g
          where g = concat["(\\ "
                          ,new n
                          ," -> "
                          ,rcall (f (inv (const (new n)))) (n+1)
                          ,")"]
                new n = "x"++show n
                
pp :: Exp -> IO ()                
pp x = putStrLn(showE x 1)      

-- We can almost write an eval, but not quite.
-- I can write it in Haskell, but not Nax since
-- Nax can't express 'apply' , 'proj1' , or 'proj2'

eval:: Exp -> Value
eval x = msfcata phi x
  where phi :: Phi E (Fix V b)
        phi rcall inv (EInt n) = In(VInt n)
        phi rcall inv (EAbs f) = In (VAbs(rcall . f . inv))
        phi rcall inv (EApp f x) = apply (rcall f) (rcall x)
          where apply (In(VAbs f)) x = f x
                -- can't be written in Nax because no eliminator for In       
        phi rcall inv (EPair x y) = In(VPair (rcall x) (rcall y))
        phi rcall inv (E1 x) = proj1(rcall x)
          where proj1 (In(VPair u v)) = u
                -- can't be written in Nax because no eliminator for In
        phi rcall inv (E2 x) = proj2(rcall x)
          where proj2 (In(VPair u v)) = v 
                -- can't be written in Nax because no eliminator for In
        
        
reify:: Value -> Exp
reify x = msfcata phi x
  where phi:: Phi V (Fix E b)
        phi rcall inv (VInt n) = In(EInt n)
        phi rcall inv (VAbs f) = In(EAbs(rcall . f . inv))
        phi rcall inv (VPair x y) = In(EPair (rcall x) (rcall y))

normalform :: Exp -> Exp
normalform x = reify (eval x) 

plus1:: Exp -> Exp
plus1 x = msfcata phi x
  where phi:: Phi E (Fix E b)
        phi rcall inv (EInt n) = In(EInt (n+1))
        phi rcall inv (EApp f x) = In(EApp (rcall f) (rcall x))
        phi rcall inv (EAbs f) = In(EAbs(rcall . f . inv))
        phi rcall inv (EPair y x) = In(EPair (rcall y) (rcall x))
        phi rcall inv (E1 x) = In(E1 (rcall x))
        phi rcall inv (E2 x) = In(E2 (rcall x))
        
-----------------------------------------------------
-- Typed terms

data T r t where
  TInt :: Int -> T r Int
  TApp :: r (a->b) -> r a -> T r b
  TAbs :: (r a -> r b) -> T r (a->b)
  TPair:: r a -> r b -> T r (a,b)
  T1:: r (a,b) -> T r a
  T2:: r (a,b) -> T r b

type Term i = forall a . FixJ T a i

tint n    = InJ (TInt n)
tapp f x  = InJ (TApp f x)
tabs f    = InJ (TAbs f)
tpair x y = InJ (TPair x y)
t1 x      = InJ (T1 x)
t2 x      = InJ (T2 x)

qi = tabs(\ f -> tabs (\ x -> tapp f x))
zi = tapp (tapp qi (tabs (\ x -> x))) (tint 6)              
wi = tapp (tapp qi (tabs (\ x -> t1 x))) (tpair (tint 33) (tint 7))


--------------------------------------------------------
-- Higher-Order, type-indexed Fixed point

data FixJ f a t = InJ (f (FixJ f a) t) | InvJ (a t)


type Theta f a =
   (forall r j . (forall i . r i -> a i) -> 
                 (forall i . a i -> r i) ->               
                 (f r j -> a j)) 
                 
cataF :: Theta f a -> (forall a . FixJ f a i) -> a i
cataF phi x = cataf phi x

cataf :: Theta f a -> FixJ f a i -> a i
cataf phi (InvJ x) = x
cataf phi (InJ x) = phi (cataf phi) InvJ x
                 
                 
unJ :: (forall a . (FixJ f a t)) -> (forall b . f (FixJ f b) t)
unJ (InJ x) = x
                 
-----------------------------------------------
-- Term t   to   Id t

data Id t = Id t deriving (Show)
unId (Id x) = x
pair (Id x) (Id y) = Id(x,y)
app (Id f) (Id x) = Id(f x)
first (Id (x,y)) = Id x
second (Id (x,y)) = Id y
                 
                 
-- Notice that the typed Term eval can be written. Here we need
-- only elimination of the non-recursive Id.  Note that the
-- self-application term (\ x -> x x) can't be written in typed Term

evalT:: Term i -> Id i
evalT x = cataF phi x
  where phi:: Theta T Id 
        phi rcall inv (TInt n) = Id n
        phi rcall inv (TPair x y) = pair (rcall x) (rcall y)
        phi rcall inv (TApp x y) = app (rcall x) (rcall y)
        phi rcall inv (TAbs f) = Id (unId . rcall . f . inv . Id)
        phi rcall inv (T1 x) = first (rcall x)
        phi rcall inv (T2 x) = second (rcall x)

--------------------------------------------------------
-- Typed terms to values

data U r i where
  UInt :: Int -> U r Int
  UAbs :: (r a -> r b ) -> U r (a -> b)
  UPair :: r a -> r b -> U r (a,b)

type Val t = forall a . FixJ U a t  

uint n = InJ (UInt n)
uabs f = InJ (UAbs f)
upair x y = InJ (UPair x y)

 
evalJ:: Term i -> Val i
evalJ x = cataF phi x
  where phi:: Theta T (FixJ U i)
        phi rcall inv (TInt n) = uint n
        phi rcall inv (TPair x y) = upair (rcall x) (rcall y)
        phi rcall inv (TAbs f) = uabs(\ x -> rcall (f (inv x)))
        phi rcall inv (TApp f x) = unfun (rcall f) (rcall x)
        phi rcall inv (T1 x) = firstu (rcall x)
        phi rcall inv (T2 x) = secondu (rcall x)

unfun:: FixJ U t1 (a -> b) -> FixJ U t1 a -> FixJ U t1 b
unfun (InJ (UAbs f)) = f

firstu:: FixJ U t1 (a,b) -> FixJ U t1 a  
firstu (InJ (UPair x y)) = x

secondu:: FixJ U t1 (a,b) -> FixJ U t1 b  
secondu (InJ (UPair x y)) = y

-----------------------------------------------------------------------
-- Can we define unfun, firstu, and secondu without pattern matching


data Less i j where
  A1 :: Less a (a -> b)
  A2 :: Less b (a -> b)
  P1 :: Less a (a,b)
  P2 :: Less b (a,b)

type Size f a =
   (forall r j . (forall i . r i -> a i) -> 
                 (forall i . Less i j -> r i -> FixJ f a i) ->
                 (forall i . Less i j -> FixJ f a i -> r i) ->
                 (f r j -> a j)) 

cataS:: Size f a -> FixJ f a j -> a j            
cataS phi (InvJ x) = x
cataS phi (InJ x) = phi (cataS phi) (\ _ x -> x) (\ _ x -> x) x

cataSz:: Size f a -> (forall a . FixJ f a j) -> a j
cataSz phi x = cataS phi x

type family F (a:: * -> *) x :: *
type instance F a (x -> y)  = (FixJ U a x -> FixJ U a y)
type instance F a (x,y) = FixJ U a (x,y)

{-
ung ::  forall t1 a b  . FixJ U t1 (a -> b) -> F t1 (a->b) 
ung x = (cataS psi x)
  where psi :: (forall r j . (forall i . r i -> F t1 i) -> 
                             (forall i . Less i j -> r i -> FixJ U (F t1) i) ->
                             (forall i . Less i j -> FixJ U (F t1) i -> r i) ->
               (U r j -> F t1 j)) 
        psi rcall cast uncast (UAbs f) = (\ x -> cast A2( f  (uncast A1 x)))




test:: (FixJ U (Zap2 t1) x -> FixJ U (Zap2 t1) y) -> Zap2 t1 (x -> y)
test f = Zap2 f


data Zap2 t1 x where
  Zap2 :: (FixJ U (Zap2 t1) a -> FixJ U (Zap2 t1) b) ->  Zap2 t1 (a -> b) 

unZap:: Zap2 t1 (a -> b) -> (FixJ U (Zap2 t1) a -> FixJ U (Zap2 t1) b)
unZap (Zap2 f) = f





data Zap x where Zap:: (FixJ U t1 a -> FixJ U t1 b) -> Zap (a -> b)
unf ::  FixJ U Zap (a -> b) -> Zap (a->b) -- FixJ U t1 a -> FixJ U t1 b
unf x = cataS psi x
  where psi :: (Size U Zap)
        psi rcall cast uncast (UAbs f) = Zap (\ x -> cast A2( f  (uncast A1 x)))
   
-}



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

lift :: (t1 -> Fix t t1) -> Fix t t1 -> Fix t t1
lift f (Inv x) = f x
lift f x = x

out:: (forall a . Fix f a) -> (forall a . f (Fix f a))
out (In x) = x

                            
          