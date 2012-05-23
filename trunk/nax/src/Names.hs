module Names(Name(..),Loc(..),SourcePos,newPos,name,bestPos
            ,ppName,noPos,toName,near,prelude,preline,augment
            ,plist,plistf,insert,pad,insertBy,dropWhite
            , nameSupply,pre,strings) where

import Data.Char(isSpace)
import Text.ParserCombinators.Parsec.Pos(SourcePos,newPos,sourceLine,sourceColumn,sourceName)
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

dropWhite xs = takeWhile (not . isSpace) (dropWhile isSpace xs)

-----------------------------------------

noPos:: SourcePos
noPos = newPos "unknown location" 0 0 

isNoPos x = (sourceName x == "unknown location") &&
            (sourceLine x == 0) &&
            (sourceColumn x == 0)
bestPos x y | isNoPos x = y
bestPos x y = x

augment (Nm(str,pos)) new augmentation = Nm(new,pos2)
  where pos2 = newPos (sourceName pos ++ augmentation) (sourceLine pos) (sourceColumn pos)

class Loc t where
  loc:: t -> SourcePos
  coord:: t -> (String,Int,Int)
  coord t = (sourceName p,sourceLine p,sourceColumn p)
    where p = loc t

near :: (Loc t) => t -> String
near exp = "near "++show(loc exp)++"\n"

prelude = newPos "Prelude" 0 0
preline n = newPos "Prelude" n 0

---------------------------------------
newtype Name = Nm (String,SourcePos)

ppName (Nm(s,pos)) = text s

name (Nm (s,p)) = s

instance Show Name where
  show (Nm(s,_)) = s
  
instance Eq Name where
  (Nm(x,_)) == (Nm(y,_)) = x==y
  
toName s = Nm(s,noPos)  

instance Ord Name where
  compare (Nm(s,_)) (Nm(t,_)) = compare s t
  
-------------------------------------


nameSupply = map pre strings 
strings = map g pairs
  where pairs = (map init "abcdefghijklmnpqrstuvwxyz") ++ map f pairs
        init c = ([c],0)
        f (s,i) = (s,i+1)
        g (x,0) = x
        g (x,n) = x ++ show n

pre s = Nm(s,newPos "prelude" 0 0)


-------------------------------------
-- formating lists of strings

plist :: Show a => String -> [a] -> String -> String -> String
plist = plistf show

plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs    

pad n s = add s
  where sn = length s
        add s = case compare n sn of
                  EQ -> s
                  GT -> s ++ replicate (n - sn) ' '
                  LT -> take n s


        
insert x [] = [x]
insert x (y:ys) | x==y = y:ys
                | x<y  = x:y:ys
                | x>y  = y:(insert x ys)

insertBy:: (a -> a -> Ordering) -> a -> [a] -> [a]                
insertBy f x [] = [x]
insertBy f x (y:ys) =
   case f x y of
     EQ -> y:ys
     LT -> x:y:ys
     GT -> y:(insertBy f x ys)                

  
  
