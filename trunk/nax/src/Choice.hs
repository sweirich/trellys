module Choice where

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

--------------------------------------------------
data Monad m => Tree m b a 
    = Fail String 
    | One a 
    | Choice b [m(Tree m b a)]
    
    
bfs [] = return []
bfs (Fail s : more) = bfs more
bfs (One x : more) = do { xs <- (bfs more); return(x:xs) }
bfs (Choice x ts : more) = 
  do { ms <- mapM id ts; bfs(more ++ ms)}


disptree:: (Monad m) => Int -> Int -> (t -> Doc) -> (a -> Doc) -> Tree m t a -> m Doc
disptree d n f g x | d > 200 = return(PP.nest n (text "..."))
disptree d n f g (Fail s) = return(PP.nest n (text ("FAIL "++s)))
disptree d n f g (One x) = return (PP.nest n (text "SOLUTION" <> g x))
disptree d n f g (Choice sub ts) = 
  do { zs <- mapM id ts
     ; ds <- mapM (disptree (d+1) (n+3) f g) zs
     ; return(PP.vcat (PP.nest n (text "CHOICE ")<> f sub : ds)) }

-------------------------------------------------
-- Trees are extensional Monads

bindTree:: Monad m => Tree m x a -> (a -> Tree m x b) -> Tree m x b
bindTree (Fail s) f = Fail s
bindTree (One a) f = f a
bindTree (Choice b tsM) f = Choice b (bindsM b tsM f)  

bindsM:: Monad m => x -> [m(Tree m x a)] -> (a -> Tree m x b) -> [m(Tree m x b)]
bindsM b xs f = [do { ts <- sequence xs; return(Choice b (binds ts f))}]

binds:: Monad m => [Tree m x a] -> (a -> Tree m x b) -> [m(Tree m x b)]
binds [] f = []
binds (Fail s : ms) f = binds ms f
binds (One a : ms) f =  return(f a) : (binds ms f)
binds (Choice b xs : ms) f = binds ms f ++ bindsM b xs f

instance Monad m => Monad (Tree m x) where
  return x = One x
  x >>= f = bindTree x f
  fail s = Fail s

------------------------------------
--  examples

one x = return(One x) 

t1:: Monad m => Tree m Int String
t1 = Choice 1 [one "A",return(Choice 2 [one "B",return(Choice 3 [return(Fail "at3"),one "C"])])]


t8:: Monad m => Tree m Int String
t8 = Choice 1 [one "A",one "C"]

t2 x = Choice 4 [return(Fail "at4")
                ,return(Choice 5 [return(Choice 6 [return(Fail "at5"),one(x,True)])
                                 ,one(x,False)])] 

t3:: Tree Maybe Int (String,Bool)
t3 = bindTree t1 t2

t4:: Tree Maybe Int (String,Bool)
t4 = bindTree t8 t2

Just d = disptree 0 0 h f t3
  where f (x,y) = PP.parens(text x <> text "," <> text(show y))
        h n = text(show n)