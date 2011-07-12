module HashCons where

import Text.ParserCombinators.Parsec.Pos(SourcePos,newPos)

import qualified Data.Map as DM
import qualified Data.Array as AR

-------------------------------------------------------
-- The monad

import qualified Control.Monad.State as MS

data Info = Info !Int
                 !(DM.Map (Shape Int) Int)
                 !(DM.Map Int (Shape Int))
                
type M a = MS.State Info a

-- generic monad operations
maybeM comp justf nothing =
  do { v <- comp; case v of { Just x -> justf x; Nothing -> nothing }}
lift1 f comp = do { x <- comp;return(f x)}    
lift2 f c1 c2 = do { x <- c1; y <- c2; return(f x y)}  
 
-------------------------------------------------------
 
next2 :: M Int
next2 = MS.mapState f (return ())
  where f ((),(Info i m1 m2)) = (i,(Info (i+1) m1 m2))

find2 :: Shape Int -> M (Maybe Int)
find2 x = MS.mapState f (return ())
  where f ((),q@(Info i tab1 tab2)) = ((lookupMemo x tab1) , q)

fetch k tab = (DM.!) tab k
 
fetch2 :: Shape Int -> M Int
fetch2 x = MS.mapState f (return ())
  where f ((),q@(Info i tab1 tab2)) = (fetch x tab1,q)  

update2 n term = MS.StateT f
  where f (Info i tab1 tab2) = return
          (n,(Info i (DM.insert term n tab1) (DM.insert n term tab2)))

shape2:: Int -> M (Shape Int)
shape2 n = MS.mapState f (return ())
  where f ((),q@(Info i tab1 tab2)) = (fetch n tab2,q)


--------------------------------------------------------
-- Hash tables

emptyMemo = DM.empty
memoInsert x tab = DM.insert x tab
lookupMemo x tab = DM.lookup x tab
memoSize x = DM.size

----------------------------------------------

data Shape t 
  = Var String
  | App t t
  | Lam String t
  | Star
  | Constr String
  | Arrow t t
 deriving (Eq,Ord,Show)
  
data Expr = E SourcePos (Shape Expr)
data HExpr = H SourcePos (Shape Int)

------------------------------------------------
--


class Functor f => Sequence f where
  swap:: Monad m => f(m a) -> m(f a)
instance Sequence [] where
  swap = sequence
instance Sequence Maybe where
  swap Nothing = return Nothing
  swap (Just m) = do { x <- m; return(Just x)}
  
instance Functor Shape where
  fmap f (Var s) = Var s
  fmap f (App x y) = App (f x) (f y)
  fmap f (Lam s x) = Lam s (f x)
  fmap f Star = Star
  fmap f (Constr c) = Constr c
  fmap f (Arrow x y) = Arrow (f x) (f y)
  
instance Sequence Shape where
  swap (Var s) = return (Var s)
  swap (App x y) = lift2 App x y
  swap (Lam s x) = lift1 (Lam s) x
  swap Star = return Star
  swap (Constr c) = return(Constr c)
  swap (Arrow x y) = lift2 Arrow x y



-------------------------------------

-- hash:: Expr -> M HExpr
hash (E pos x) = 
  do { y <- swap(fmap hash x)
     ; maybeM (find2 y) return undefined
     }
   