module Terms2 where 

import Text.Parsec.Pos(SourcePos,newPos)


import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)
import Data.List((\\),union,unionBy)

import Names
import BaseTypes
import Syntax2
import Value
-- import Types(patBinds)
import Monads(Id,runId,lift1)

  
       
---------------------------------------------------------------
-- How to deal with N-tuples

patTuple :: [Pat n t ] -> Pat n t     -- Form a Pat like (x,y:ys)
patTuple [] = PLit prelude LUnit     -- (x,y,z,w) --> (x,(y,(z,w)))
patTuple [p] = p
patTuple ps = PTuple ps

expTuple :: [PExpr] -> PExpr   -- Form an Expression with is a tuple like (3,4-9)
expTuple [] = PELit prelude LUnit
expTuple [p] = p
expTuple es = PETuple es

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


unitExp = PELit noPos LUnit
consExp x y = PEIn Star (PEApp (PEApp (PECon (Nm("Cons",prelude))) x) y)
nilExp =  PEIn Star (PECon (Nm("Nil",prelude)))
listExp  = foldr consExp nilExp
trueExp  = PECon (Nm("True",prelude))    -- EVar (Nm("True",prelude))
falseExp = PECon (Nm("False",prelude))  -- EVar (Nm("False",prelude))




caseExp x ms = PEApp (PEAbs ElimConst ms) x
ifExp x y z = caseExp x [(truePat,y),(falsePat,z)]

applyE :: [PExpr] -> PExpr
applyE [t] = t
applyE [x,y] = PEApp x y
applyE (f:x:xs) = applyE (PEApp f x : xs)

 

abstract :: [Pat Name PTyp] -> PExpr -> PExpr
abstract [] body = body
abstract (p:ps) body = PEAbs ElimConst [(p,abstract ps body)]

binop nm e1 e2 = applyE [PEVar UNIV nm,e1,e2]

isTruth (VCon _ 0 "True" []) = True
isTruth _ = False

unLit (VBase pos x) = x
unLit v = error ("Non base type:\n   "++show v)


--------------------------------------------

-----------------------------------------
-- computing free variables

                       
freeExp (PELit _ _) ans = ans
freeExp (PEVar _ n) ans = insert (name n) ans
freeExp (PECon n) ans = (insert (name n) ans)
freeExp (PEApp f x) ans = freeExp f (freeExp x ans)
freeExp (PEAbs elim ps) ans = foldr g ans ps
  where g (p,e) ans = freeExp e ans \\ (map name bound)
          where (bound) = patBinds p ([])          
freeExp (PELet d e) ans = (freeExp e ans2) \\ bound where (ans2,bound,newTypCon) = freeDec d ans
freeExp (PETuple xs) ans = foldr freeExp ans xs
freeExp (PEIn k x) ans = freeExp x ans
-- freeExp (ECon pos c xs) ans = foldr freeExp ans xs
-- freeExp (ETyApp exp typ) ans = error "No freeExp for ETyApp yet"
-- freeExp (ETyAbs ty e) ans = (freeExp e ans) \\ [name ty]
freeExp (PEMend s elim e ms) ans = error "No freeExp for EMend yet"
-- freeExp (Emv _) ans = error "No freeExp for Emv yet"


-- freeDec d ans ---> (appear free,binds at value, binds at types)

freeDec (Def _ p e) ans = (freeExp e ans,map name binds,[])
  where (binds) = patBinds p ([])  
freeDec (DataDec p nm args cs derivs) ans = (ans,map (name . fst) cs,[nm])
freeDec (GADT p nm free kind cs derivs) ans = (ans,map f cs,[nm])
   where f (c,vs,doms,rng) = name c
freeDec (FunDec p nm ts rhs) ans = (error ("Not yet freeDec") ans,[nm],[])


------------------------------------------------------

