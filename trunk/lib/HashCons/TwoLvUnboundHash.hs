{-# LANGUAGE MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
           , TypeSynonymInstances #-}

module TwoLevelUnbound where

import Unbound.LocallyNameless -- hiding (CON,Val)
-- import Unbound.LocallyNameless.Alpha(aeqR1)
-- import Unbound.LocallyNameless.Ops(unsafeUnbind)

import Control.Monad
import Data.Maybe
import Text.ParserCombinators.Parsec.Pos(SourcePos,newPos)

import qualified Data.Map as DM
import qualified Data.Array as AR
import qualified Control.Monad.State as MS

----------------------------------------------
-- Two level Exprs

-- The non-recursive level

data Shape nm t
  = Var nm
  | App t t
  | Lam (Bind nm t)
  | Star
  | CON String
  | Arr t t
 deriving Show
-- deriving (Eq,Ord,Show)

-- Tie the recursive knot, note the SourcePos is argument of E

data Expr = E SourcePos (Shape (Name Expr) Expr) deriving Show

$(derive [''Shape,''SourcePos,''Expr])

instance Alpha SourcePos
instance Alpha (Shape (Name Expr) Expr)
instance Alpha Expr

instance Subst Expr SourcePos where
  isvar _ = Nothing

instance Subst Expr (Shape (Name Expr) Expr) where
   isvar (Var v) = error "I blieve it should not reach" -- Just (SubstName v)
   isvar _       = Nothing

instance Subst Expr Expr where
  isvar (E _ (Var v)) = Just (SubstName v)
  isvar _             = Nothing

-- Simple 1 level constructors

var s = E p1 (Var $ string2Name s)
app x y = E p1 (App x y)
lam s t = E p1 (Lam $ bind (string2Name s) t)
star = E p1 Star
con s = E p1 (CON s)
arr x y = E p1 (Arr x y)
 
-- some examples

p1 = newPos "Test" 0 0
x = var "x"
y = var "y"
z = var "z"

e1 = app (arr x y) (lam "z" (arr x y))

------------------------------------------------
-- operations on Shapes

-- everything should come into LFresh monad???

{-
class (Fresh m, Alpha nm) => MFunctor m f nm where
  mfmap :: (Alpha a, Alpha b) => (a -> m b) -> f nm a -> m (f nm b)


instance (Fresh m, Alpha nm) => MFunctor m Bind nm where
  mfmap = undefined -- mfmapBind

instance (Fresh m, Alpha nm) => MFunctor m Shape nm where
  mfmap = mfmapShape


mfmapExpr f (E sp shape) = do shape' <- mfmapShape f shape
                              return (E sp shape')

mfmapBind f bnd =
  do (p,t) <- unbind bnd
     t' <- mfmapExpr f t
     return (bind p t')

mfmapShape f shape =
  case shape of
    Var s -> return (Var s)
    App x y -> liftM2 App (f x) (f y)
    Lam x -> do x' <- mfmapBind f x
                return (Lam x')
    Star -> return Star
    CON c -> return (CON c)
    Arr x y -> liftM2 Arr (f x) (f y)





instance Functor (Bind (Name Expr)) where
  fmap f = undefined -- TODO what is the functor for Bind ???

instance Functor (Bind nm) => Functor (Shape nm) where
  fmap f (Var s) = Var s
  fmap f (App x y) = App (f x) (f y)
  fmap f (Lam x) = Lam (fmap f x)
  fmap f Star = Star
  fmap f (CON c) = CON c
  fmap f (Arr x y) = Arr (f x) (f y)

instance Functor (Bind nm) => Sequence (Shape nm) where
  swap (Var s) = return (Var s)
  swap (App x y) = liftM2 App x y
--  swap (Lam x) = liftM Lam x -- this is a type error !!!
  swap Star = return Star
  swap (CON c) = return(CON c)
  swap (Arr x y) = liftM2 Arr x y
-}

--------------------------------------------------------
-- Generic operations on memoizing Tables

emptyMemo = DM.empty
memoInsert x tab = DM.insert x tab
lookupMemo x tab = DM.lookup x tab
memoSize x = DM.size

fetch :: Ord k => k -> DM.Map k a -> a
fetch k tab = (DM.!) tab k
 
---------------------------------------------------
-- generic monad operations

class Functor f => Sequence f where
  swap:: Monad m => f(m a) -> m(f a)
instance Sequence [] where
  swap = sequence
instance Sequence Maybe where
  swap Nothing = return Nothing
  swap (Just m) = do { x <- m; return(Just x)}
{- 
-------------------------------------------------------
-- The first monad

data Info = Info !Int
                 !(DM.Map (Shape Int) Int)
                 !(DM.Map Int (Shape Int))
                
type M a = MS.State Info a

runM :: M a -> (a, Info)
runM x = MS.runState x (Info 1 emptyMemo emptyMemo)

showM x = (unlines(show root : map f is))
  where (root,Info next tab1 tab2) = runM x
        is = DM.assocs tab2
        f (i,shape) = show i++"  "++show shape
        
instance Show a => Show(M a) where
  show x = showM x

-------------------------------------------------------
-- Operations in the first Monad

nextM :: M Int
nextM = MS.mapState f (return ())
  where f ((),(Info i m1 m2)) = (i,(Info (i+1) m1 m2))

findM :: Shape Int -> M (Maybe Int)
findM x = MS.mapState f (return ())
  where f ((),q@(Info i tab1 tab2)) = ((lookupMemo x tab1) , q)


fetchM :: Shape Int -> M Int
fetchM x = MS.mapState f (return ())
  where f ((),q@(Info i tab1 tab2)) = (fetch x tab1,q)  

updateM :: Monad m => Int -> Shape Int -> MS.StateT Info m Int
updateM n term = MS.StateT f
  where f (Info i tab1 tab2) = return
          (n,(Info i (memoInsert term n tab1) (memoInsert n term tab2)))

shapeM:: Int -> M (Shape Int)
shapeM n = MS.mapState f (return ())
  where f ((),q@(Info i tab1 tab2)) = (fetch n tab2,q)



----------------------------------------------
-- Approach 1, store everything in a table
-- and pass around just a pointer into the table

data HExpr = H SourcePos Int   -- the pointer 
  deriving Show

index:: Expr -> M Int
index (E pos x) = 
   do { shape <- swap(fmap index x)
      ; maybeM (findM shape) return
         (do { new <- nextM; updateM new shape; return new})
      }
      
hash :: Expr -> M HExpr
hash (term@(E pos x)) = do {i <- index term; return(H pos i)}

instance Eq HExpr where
  (H p i) == (H q j) = i==j

unindex:: Int -> M Expr
unindex i = 
  do { sh <- shapeM i                -- sh:: Shape Int
     ; shE <- swap(fmap unindex sh)  -- shE:: Shape Expr
     ; return(E p1 shE)}

unHash :: HExpr -> M Expr     
unHash (H p i) = unindex i     

{-
e1 = app (arr x y) (lam "z" (arr x y))

*HashCONs> hash e1
H "Test" (line 0, column 0) 5
1  Var "x"
2  Var "y"
3  Arr 1 2
4  Lam "z" 3
5  App 3 4

Notes.

1) Note the sharing of node:  3  Arr 1 2

2) Note that position information is lost (except at the top node) since
shared nodes would have multiple positions. We cound track this with
another table.

3) Matching against a term is computational, 
we need to look up the shape in the memo table.
And matching is at most one level deep.

4) Equality is a constant time operation

5) We can abstract away from the actual Shape, so the
function above would work on any shape.

-}

--------------------------------------------------------
-- Approach 2, Build a deep tree, but tag every node
-- with a unique index. Only the first tree built is
-- stored, and subsequent trees are replaced by the first
-- tree.

-------------------------------------------------------
-- The second monad

data Table = Table !Int
                   !(DM.Map (Shape Int) Int)
                   !(DM.Map Int DExpr)
                
type M2 a = MS.State Table a

runM2 :: M2 a -> (a, Table)
runM2 x = MS.runState x (Table 1 emptyMemo emptyMemo)

showM2 x = (unlines(show root : map f is))
  where (root,Table next tab1 tab2) = runM2 x
        is = DM.assocs tab2
        f (i,shape) = show i++"  "++show shape
        
instance Show a => Show(M2 a) where
  show x = showM2 x
  
nextM2 :: M2 Int
nextM2 = MS.mapState f (return ())
  where f ((),(Table i m1 m2)) = (i,(Table (i+1) m1 m2))

findM2 :: Shape Int -> M2 (Maybe Int)
findM2 x = MS.mapState f (return ())
  where f ((),q@(Table i tab1 tab2)) = ((lookupMemo x tab1) , q)
  
shapeM2:: Int -> M2 DExpr
shapeM2 n = MS.mapState f (return ())
  where f ((),q@(Table i tab1 tab2)) = (fetch n tab2,q)
  
updateM2 :: Int -> Shape DExpr -> M2 DExpr
updateM2 n term = MS.StateT f
  where f (Table i tab1 tab2) = return
          (D n term,(Table i (memoInsert (fmap uniq term) n tab1) 
                             (memoInsert n (D n term) tab2)))
                             
-----------------------------------------------------
-- The datatype for the second approach

data DExpr = D Int (Shape DExpr)

uniq (D i x) = i

instance Eq DExpr where
  (D i _) == (D j _) = i==j
  
instance Show DExpr where
  show (D i (Var s)) = s
  show (D i (App x y)) = "("++show x++" "++show y++")"
  show (D i (Arr x y)) = "("++show x++" -> "++show y++")"  
  show (D i Star) = "*"
  show (D i (CON c)) = "%"++c
  show (D i (Lam x y)) = "(Lam "++x++"."++show y++")"  
  
  
hash2:: Expr -> M2 DExpr
hash2 (E pos x) = 
  do { shape <- swap(fmap hash2 x)
     ; maybeM (findM2 (fmap uniq shape))
              shapeM2 
              (do { i <- nextM2; updateM2 i shape})
     }   

{-
e1 = app (arr x y) (lam "z" (arr x y))

*HashCONs> hash2 e1
((x -> y) (Lam z.(x -> y)))
1  x
2  y
3  (x -> y)
4  (Lam z.(x -> y))
5  ((x -> y) (Lam z.(x -> y)))

Notes

1) We get the complete deep term, but the common subterms
are only stored once. The unique tag can tell which terms
are equal.

-}
  
  
 -} 
  
  
