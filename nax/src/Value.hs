{-# LANGUAGE PatternGuards, MultiParamTypeClasses, 
    FlexibleInstances, ScopedTypeVariables #-}

module Value where

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)
import Data.List(elemIndex)
import qualified Data.Map as DM 

import Data.IORef(newIORef,readIORef,writeIORef,IORef)

import Names
import BaseTypes
import Syntax
{-
import Types(tMu,tint,tbool,arrT,applyT,tstring,tunit
            ,tinteger,tdouble,tchar,tbool,maybeT,eitherT
            ,listT,tarr, tupleT) 
-}
import Monads(FIO)            

-------------------------------------------------
-- Types of values

typeNameVal :: Value m -> String
typeNameVal (VBase pos x)   = typeNameLit x
typeNameVal (VFun typ g)    = "? -> ?"
typeNameVal (VFunM n g)    = "? => ?"
typeNameVal (VTuple vs) = plistf typeNameVal "(" vs "," ")"
typeNameVal (VCon _ arity c vs) = "T?"
typeNameVal (VIn k x) = "Mu "++typeNameVal x
typeNameVal (VInverse x) = "?"
 
commafy [] = PP.empty
commafy [x] = x
commafy (x:xs) = x <> text "," <> commafy xs

--------------------------------------------------------   

class Typable t where
  encodingTyp :: t -> Typ

class Typable t => Encoding t m where
   to     :: t -> Value m
   from   :: Value m -> t

-----------------------------------------
-- Base instances

instance Typable () where   
   encodingTyp _ = tunit

instance Typable Int where
    encodingTyp _ = tint

instance Typable Integer where
    encodingTyp _ = tinteger

instance Typable Double where
    encodingTyp _ = tdouble

instance Typable Char where
    encodingTyp _ = tchar

instance Encoding () m where
   to x = VBase noPos LUnit
   from (VBase pos LUnit) = ()
   from v = error ("Value not unit: "++(show v))
   
instance Encoding Int m where
    to n = VBase noPos (LInt n)
    from (VBase noPos (LInt n)) = n
    from v = error ("Value not an Int: "++(show v))
    
instance Encoding Integer m where
    to n = VBase noPos (LInteger n)
    from (VBase noPos (LInteger n)) = n
    from v = error ("Value not an Integer: "++(show v))

instance Encoding Double m where
    to n = VBase noPos (LDouble n)
    from (VBase noPos (LDouble n)) = n
    from v = error ("Value not a Double: "++(show v))

instance Encoding Char m where
    to n = VBase noPos (LChar n)
    from (VBase noPos (LChar n)) = n
    from v = error ("Value not a Char: "++(show v))

baseToTyp:: Base -> Typ
baseToTyp Int = tint
baseToTyp Integer = tinteger
baseToTyp Double = tdouble
baseToTyp Char = tchar
baseToTyp Unit = tunit

btype x = baseToTyp(base x)
   
---------------------------------
-- datatype instances

conKeyMap = [("True",None)
            ,("False",None)
            ,("Nothing",None)
            ,("Just",None)
            ,("Left",None)
            ,("Right",None)
            ,("Nil",Syn "n")
            ,("Cons",Syn "n")]

conkeyM x = lookup x conKeyMap

conkey x = 
  case conkeyM x of
    Just n -> n
    Nothing -> error("Predefined constructor function not assigned a key: "++show x)
    

instance Encoding (Value m) m where
    to x = x
    from x = x
    
instance Typable (Value m) where    
    encodingTyp _ = error ("encoding type of Value is polymorphic")

---
instance Encoding Bool m where
    to True = (VCon (conkey "True") 0 "True" [])
    to False = (VCon (conkey "False") 0 "False"  [])
    from (VCon _ 0 "True" []) = True
    from (VCon _ 0 "False" []) = False
    from v = error ("Value not Bool: "++(show v))

instance Typable Bool where
    encodingTyp _ = tbool

---
instance Encoding a m => Encoding (Maybe a) m where
    to Nothing = VCon (conkey "Nothing") 0 "Nothing" []
    to (Just x) = VCon (conkey "Just") 1 "Just" [to x]
    from (VCon _ 0 "Nothing" []) = Nothing
    from (VCon _ 1 "Just" [x]) = (Just (from x))
    from v = error ("Value not a Maybe type: "++show v)

instance Typable a => Typable (Maybe a) where
    encodingTyp ~(Just x) = maybeT (encodingTyp x)
       
---
instance (Encoding a m,Encoding b m) => Encoding (Either a b) m where
    to (Right x) =  (VCon (conkey "Right") 1 "Right" [to x])
    to (Left x) =   (VCon (conkey "Left") 1 "Left" [to x])
    from (VCon _ 1 "Left" [x]) = Left(from x)
    from (VCon _ 1 "Right" [x]) = Right(from x)
    from v = error ("Value not an Either type: "++show v)

instance (Typable a,Typable b) => Typable (Either a b) where
    encodingTyp x = eitherT (encodingTyp (left x)) (encodingTyp (right x))
      where left :: Either a b -> a
            left _ = (error "impossible Typable Either left")
            right :: Either a b -> b
            right _ = (error "impossible Typable Either right")

---- Lists
instance Encoding a m => Encoding [a] m where
    to x = listVal (map to x)
    from x | Just vs <- isValueList x = map from vs
           | True = error("Value not a list: "++show x)
  
instance Typable a => Typable [a]  where
  encodingTyp ~(x:xs) = listT (encodingTyp x)


listVal vs = foldr cons nil vs
  where -- cons (VBase (LChar c)) (VCon 0 "[]" []) = VBase(LString [c])
        -- cons (VBase (LChar c)) (VBase(LString cs)) = VBase(LString (c:cs))
        cons x xs = VIn Star (VCon (conkey "Cons") 2 "Cons" [x,xs])
        nil = VIn Star (VCon (conkey "Nil") 0 "Nil" [])  

isIntList (VIn k (VCon _ 0 "Nil" [])) = return []
isIntList (VIn k (VCon _ 2 "Cons" [VBase noPos (LInt x),xs])) =
  do { ys <- isIntList xs; return(x:ys)}
isIntList _ = Nothing 


-------------------------------------------
-- tuple instances 

instance (Encoding a m,Encoding b m) => Encoding (a,b) m where
    to (a,b) = VTuple[to a,to b]
    from (VTuple[x,y]) = (from x,from y)
    from v = error ("Value not a pair: "++(show v))

instance (Typable a,Typable b) => Typable(a,b) where
    encodingTyp ~(x,y) = tupleT [encodingTyp x, encodingTyp y]

---
instance (Encoding a m,Encoding b m,Encoding c m) => Encoding (a,b,c) m where
    to (a,b,c) = VTuple[to a, to b, to c]
    from (VTuple[x,y,z]) = (from x,from y,from z)
    from v = error ("Value not a triple: "++(show v))

instance (Typable a,Typable b,Typable c) => Typable(a,b,c) where
    encodingTyp ~(w,x,y) = tupleT [encodingTyp w,encodingTyp x, encodingTyp y]
    
instance (Encoding a m,Encoding b m,Encoding c m,Encoding d m) => Encoding (a,b,c,d) m where
    to (a,b,c,d) = VTuple[to a, to b, to c, to d]
    from (VTuple[w,x,y,z]) = (from w,from x,from y,from z)
    from v = error ("Value not a quadruple: "++(show v))

instance (Typable a,Typable b,Typable c, Typable d) => Typable(a,b,c,d) where
    encodingTyp ~(w,x,y,z) = tupleT [encodingTyp w,encodingTyp x, encodingTyp y,encodingTyp z]

--------------------------------------------
-- function instances

instance (Encoding a m,Encoding b m) => Encoding(a -> b) m where
    -- works on first order functions only
    to f = VFun (encodingTyp ((error "impossible encodin -> ")::a)) (\ x -> to(f(from x)))
    from (VFun typ f) = from . f . to 
    from (VFunM n f) = error ("'from' for monadic functions not defined.")
    from x = error("Value not a function: "++show x)

instance (Typable a ,Typable b ) => Typable(a -> b) where
    encodingTyp x = arrT (encodingTyp ((error "impossible typable ->")::a)) (encodingTyp (undefined::b))
    

-- Creating values encoding functions in a computational monad

liftM1 typ n f = VFunM n (\ x k -> do { ans <- f(from x); k(to ans)})
liftM2 t1 t2 n f = (VFun t1(\ x -> liftM1 t2 n (f (from x))))
    
liftIII :: (Int -> Int -> Int) -> (Value m,Scheme)
liftIII f = (to f,Sch [] (Tau(tint `arrT` (tint `arrT` tint))))

liftIIB :: (Int -> Int -> Bool) -> (Value m,Scheme)
liftIIB f = (to f,Sch [] (Tau(tint `arrT` (tint `arrT` tbool))))

liftBBB :: (Bool -> Bool -> Bool) -> (Value m,Scheme)
liftBBB f = (to f,Sch [] (Tau(tbool `arrT` (tbool `arrT` tbool))))

liftBB :: (Bool -> Bool) -> (Value m,Scheme)
liftBB f = (to f,Sch [] (Tau(tbool `arrT` tbool)))

---------------------------------------------------------------
-- defining the primitive and prefined functions and data

imply False _ = True
imply True x = x

prims = [("+"  ,liftIII (+))
        ,("-"  ,liftIII (-))
        ,("*"  ,liftIII (*))
        ,("/"  ,liftIII (div))
        ,("&&" ,liftBBB (&&))
        ,("||" ,liftBBB (||))
        ,("not",liftBB  not)
        ,("=>" ,liftBBB imply)
        ,("<"  ,liftIIB (<))
        ,("<=" ,liftIIB (<=))
        ,(">=" ,liftIIB (>=))
        ,(">"  ,liftIIB (>))
        ,("==" ,liftIIB (==))
        ,("/=" ,liftIIB (/=))
        ]

traceScheme =  Sch [(x,Type Star)] (Tau (tstring `arrT` (xt `arrT` xt)))
  where x = Nm("a",noPos)
        xt = TyVar x Star

showScheme =  Sch [(x,Type Star)] (Tau (xt `arrT` tstring))
  where x = Nm("t",noPos)
        xt = TyVar x Star     

preDefinedDeclStrings =
          [ -- "data N r = Zero | Succ r deriving  fixpoint Nat"
           "data N: * -> * where { Zero: N a; Succ: a -> N a } deriving  fixpoint Nat"
          ,"data L a r = Nil | Cons a r deriving fixpoint List"       
          ,"data Bool = False | True"
          ,"data Either a b = Left a | Right b"
          ,"data Maybe a = Nothing | Just a"
        --  ,"data Monad (m:: * -> *) = Mon (forall a .a -> m a) (forall a b . m a -> (a -> m b) -> m b)(forall a . (List Char) -> m a)"
        --  ,"nil = In * N"
        --  ,"cons x xs = In * (C x xs)"
        --  ,"z = In * Z"
        --  ,"s x = In * (S x)"
      
       ]

injectIII :: String -> Int -> (Int -> Int -> Int) -> ((Name,Integer,Value IO),(Name,Scheme))
injectIII str n f = (triple,(name,scheme))
  where triple = (name,toInteger n,VFun tint v0)
        fexp = CSP triple
        name = Nm(str,preline n)
        scheme = Sch [] (Tau(encodingTyp f))
        v0 (VCode x) = VFun tint (e1 x)
        v0 (VBase pos (LInt n)) = VFun tint (v1 n)
        v0 v = error (str++" applied to non Int: "++show v)

        v1 n (VCode x) = VCode(applyTE[fexp,int n,x])
        v1 n (VBase pos (LInt m)) = VBase noPos (LInt (f n m))       
        v1 n v = error ("("++str++" "++show n++") applied to non Int: "++show v)

        e1 x (VCode y) = VCode(applyTE[fexp,x,y]) 
        e1 x (VBase pos (LInt m)) = VCode(applyTE[fexp,x,int m])   
        e1 x v = error ("("++str++" "++show x++") applied to non Int: "++show v)
        
        int n = TELit noPos (LInt n)
        
injectBBB :: String -> Int -> (Bool -> Bool -> Bool) -> ((Name,Integer,Value IO),(Name,Scheme))
injectBBB str n f = (triple,(name,scheme))
  where triple = (name,toInteger n,VFun tbool v0)
        fexp = CSP triple
        name = Nm(str,preline n)
        scheme = Sch [] (Tau(encodingTyp f))

        v0 (VCode x) = VFun tbool (e1 x)
        v0 (VCon _ 0 "True" []) = VFun tbool (v1 True)
        v0 (VCon _ 0 "False" []) = VFun tbool (v1 False)
        v0 v = error (str++" applied to non Bool: "++show v)

        v1 True (VCode x) = VCode(applyTE[fexp,trueTExp,x])
        v1 False(VCode x) = VCode(applyTE[fexp,falseTExp,x])        
        v1 n (VCon _ 0 "True" []) = to(f n True)
        v1 n (VCon _ 0 "False" []) = to(f n False)       
        v1 n v = error ("("++str++" "++show n++") applied to non Bool: "++show v)

        e1 x (VCode y) = VCode(applyTE[fexp,x,y]) 
        e1 x (VCon _ 0 "True" [])  = VCode(applyTE[fexp,x,trueTExp])
        e1 x (VCon _ 0 "False" []) = VCode(applyTE[fexp,x,falseTExp])
        e1 x v = error ("("++str++" "++show x++") applied to non Bool: "++show v)
        
injectIIB :: String -> Int -> (Int -> Int -> Bool) -> ((Name,Integer,Value IO),(Name,Scheme))
injectIIB str n f = (triple,(name,scheme))
  where triple = (name,toInteger n,VFun tint v0)
        fexp = CSP triple
        name = Nm(str,preline n)
        scheme = Sch [] (Tau(encodingTyp f))
        v0 (VCode x) = VFun tint (e1 x)
        v0 (VBase pos (LInt n)) = VFun tint (v1 n)
        v0 v = error (str++" applied to non Bool: "++show v)

        v1 i (VCode x) = VCode(applyTE[fexp,int i,x])  
        v1 n (VBase pos (LInt m)) = to (f n m)
        v1 n v = error ("("++str++" "++show n++") applied to non Bool: "++show v)

        e1 x (VCode y) = VCode(applyTE[fexp,x,y]) 
        e1 x (VBase pos (LInt m)) = VCode(applyTE[fexp,x,int m])  
        e1 x v = error ("("++str++" "++show x++") applied to non Bool: "++show v)  
        
        int n = TELit noPos (LInt n)
        
        
notInfo n = (triple,(name,scheme))
  where triple = (name,toInteger n,VFun tbool v0) 
        fexp = CSP triple
        name = Nm("not",preline n)
        scheme = Sch [] (Tau(encodingTyp not))  
        v0 (VCode x) = VCode(applyTE[fexp,x])
        v0 (VCon _ 0 "True" []) =  to False
        v0 (VCon _ 0 "False" []) = to True
        v0 v = error ("not applied to non Bool: "++show v)
                
trueTExp = TECon None (toName "True") (Tau tbool) 0 [] 
     -- CSP(toName "True",conkey "True",to True)
falseTExp = TECon None (toName "False") (Tau tbool) 0 [] 
     -- CSP(toName "False",conkey "False",to False)
        
applyTE :: [TExpr] -> TExpr
applyTE [t] = t
applyTE [x,y] = TEApp x y
applyTE (f:x:xs) = applyTE (TEApp f x : xs)

        
                

