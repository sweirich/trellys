module Terms where 

import Text.Parsec.Pos(SourcePos,newPos)


import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)
import Data.List((\\),union,unionBy)

import Names
import BaseTypes
import Syntax
import Value
-- import Types(patBinds)
import Monads(lift1)

  
       
---------------------------------------------------------------
-- How to deal with N-tuples

patTuple :: [Pat] -> Pat     -- Form a Pat like (x,y:ys)
patTuple [] = PLit prelude LUnit     -- (x,y,z,w) --> (x,(y,(z,w)))
patTuple [p] = p
patTuple ps = PTuple ps

expTuple :: [Expr] -> Expr   -- Form an Expression with is a tuple like (3,4-9)
expTuple [] = ELit prelude LUnit
expTuple [p] = p
expTuple es = ETuple es

valTuple :: [Value m] -> Value m
valTuple [] = VBase noPos LUnit
valTuple [x] = x
valTuple xs = VTuple xs

-- Making Patterns and Expressions

truePat  = PCon (Nm("True",prelude)) []
falsePat = PCon (Nm("False",prelude)) []

{-
-- can't match against lists, this implies use of 'out'
patNil = PCon (Nm("[]",prelude)) []
pConsUp pnil [] = pnil
pConsUp pnil (p:ps) = PCon (Nm(":",prelude)) [p,pConsUp pnil ps]
-}


unitExp = ELit noPos LUnit
consExp x y = EIn Star (EApp (EApp (ECon (Nm("Cons",prelude))) x) y)
nilExp =  EIn Star (ECon (Nm("Nil",prelude)))
listExp  = foldr consExp nilExp
trueExp  = ECon (Nm("True",prelude))    -- EVar (Nm("True",prelude))
falseExp = ECon (Nm("False",prelude))  -- EVar (Nm("False",prelude))




caseExp x ms = EApp (EAbs ElimConst ms) x
ifExp x y z = caseExp x [(truePat,y),(falsePat,z)]

applyE :: [Expr] -> Expr
applyE [t] = t
applyE [x,y] = EApp x y
applyE (f:x:xs) = applyE (EApp f x : xs)

 

abstract :: [Pat] -> Expr -> Expr
abstract [] body = body
abstract (p:ps) body = EAbs ElimConst [(p,abstract ps body)]

binop nm e1 e2 = applyE [EVar nm,e1,e2]

isTruth (VCon _ 0 "True" []) = True
isTruth _ = False

unLit (VBase pos x) = x
unLit v = error ("Non base type:\n   "++show v)


--------------------------------------------

-----------------------------------------
-- computing free variables

                       
freeExp (ELit _ _) ans = ans
freeExp (EVar n) ans = insert (name n) ans
freeExp (EFree n) ans = ans  -- Efree things will elaborate to CSP constants
freeExp (ECon n) ans = (insert (name n) ans)
freeExp (EApp f x) ans = freeExp f (freeExp x ans)
freeExp (EAbs elim ps) ans = foldr g ans ps
  where g (p,e) ans = freeExp e ans \\ (map name bound)
          where (bound) = patBinds p ([])          
freeExp (ELet d e) ans = (freeExp e ans2) \\ bound where (ans2,bound,newTypCon) = freeDec d ans
freeExp (ETuple xs) ans = foldr freeExp ans xs
freeExp (EIn k x) ans = freeExp x ans
-- freeExp (ECon pos c xs) ans = foldr freeExp ans xs
-- freeExp (ETyApp exp typ) ans = error "No freeExp for ETyApp yet"
-- freeExp (ETyAbs ty e) ans = (freeExp e ans) \\ [name ty]
freeExp (EMend s elim e ms) ans = error "No freeExp for EMend yet"
-- freeExp (Emv _) ans = error "No freeExp for Emv yet"


-- freeDec d ans ---> (appear free,binds at value, binds at types)

freeDec (Def _ p e) ans = (freeExp e ans,map name binds,[])
  where (binds) = patBinds p ([])  
freeDec (DataDec p nm args cs derivs) ans = (ans,map (name . fst) cs,[nm])
freeDec (GADT p nm kind cs derivs) ans = (ans,map f cs,[nm])
   where f (c,vs,doms,rng) = name c
freeDec (FunDec p nm ts rhs) ans = (error ("Not yet freeDec") ans,[nm],[])


------------------------------------------------------

