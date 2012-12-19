{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module Eval where

import Data.List(isInfixOf)
import System.IO(fixIO)
-- import Debug.Trace(trace)
import Data.Functor.Identity

import UniqInteger
import Names
import Syntax
import BaseTypes
import Terms(freeExp)
import Value(Encoding(..),Typable(..),traceScheme,showScheme,prims,imply,applyTE
            ,injectIII,injectBBB,injectIIB,notInfo,conkeyM)
-- import Types(patBinds,tint,tbool,arrT)
import Monads(FIO,fio,freshNameIO)
-- Miscellaneous stuff

import Control.Monad(foldM,liftM,liftM2,liftM3)
import qualified Data.Map as DM
import Data.Map (fromListWith)
import Data.List(elemIndex)
import Text.Parsec.Pos(SourcePos,newPos)


----------------------------------
-- environments


data VEnv   = VEnv { rtbindings:: [(Name,Integer,Value IO)]
                   , ctbindings:: [(Name, Class Kind Typ TExpr)] }

instance Show (VEnv) where
  show x = (plistf id "(" (map f (rtbindings x)) "," ")")
    where f (Nm (nm,p),uniq,val) = nm

browse:: String -> VEnv -> String     
browse n venv = plistf id "\n" strings "\n" "\n"
  where select (Nm(s,loc),i,v) = (s,loc,v)
        p (s,loc,v) = isInfixOf n s
        pairs = filter p (map select (rtbindings venv))
        max = maximum (0 : map (\(x,y,z)-> length x) pairs)
        strings = map f pairs
        f (s,loc,v) = pad (max+1) s ++ show loc ++ " " ++ show v

-----------------------------------------------------------
-- matching

type Sub m = [(Name,Value m)]

match:: Sub m -> Pat -> Value m -> Maybe (Sub m)
match s p v = help s p v where
  help s (PVar nm _) v = Just((nm,v):s)
  help s (PWild pos) v = Just s
  help s (PLit pos c) v = if v==(VBase pos c) then Just s else Nothing
  help s (PTuple ps) (VTuple vs) | (length ps==length vs)= thread s ps vs
  -- help s (PSum j x) (VSum i v) | i==j = match s x v
  help s (PCon (Nm(c,_)) ps) (VCon i arity d vs) | (c==d) = thread s ps vs
  help s p v = Nothing

thread :: Sub m -> [Pat] -> [Value m] -> Maybe (Sub m)
thread s [] [] = Just s
thread s (p:ps) (v:vs) = 
   case match s p v of
     Just s' -> thread s' ps vs
     Nothing -> Nothing
     

evalMVar:: [(Name,Integer,Value m)] -> Name -> [(Name,Integer,Value m)] -> IO(Integer,Value m)
evalMVar all nm [] = 
     fail (near nm++"Variable not found: "++show (name nm) ++
            plistf (\(nm,_,v) -> show nm++":"++show v) "\n  " (take 6 all) "\n  " "")
evalMVar all nm ((name,uniq,v):more) =
  if nm==name then return (uniq,v) else evalMVar all nm more

extendEnvName vs env = env{rtbindings=(vs ++ rtbindings env)
                          ,ctbindings=(map f vs ++ ctbindings env)} 
  where f (x@(nm,i,v)) = (nm,Exp(CSP x))
  
matchM:: VEnv -> Pat -> Value IO -> IO(Maybe (VEnv))
matchM env p v = 
     case (match [] p v) of
       Just pairs -> do { us <- mapM new pairs; return(Just (extendEnvName us env))}
       Nothing -> return Nothing
  where new (nm,v) = do { u <- nextinteger; return(nm,u,v)}


----------------------------------------------------
apply:: TExpr -> TExpr -> Value IO -> Value IO -> (Value IO -> IO a) -> IO a
apply g y fun arg k = 
    do { -- println("\napply: ("++show (EApp g [y])++"). "++show fun++" "++show arg);
        app (show(TEApp g y)) fun arg k }
        
app tag (VFunM n vf) x k = vf x k
app tag (VFun ty g) x k = k(g x)
app tag (VCon i arity c vs) v k | arity > length vs = k(VCon i arity c (vs ++ [v]))
app tag (VCode fun) v k = do { arg <- reify Nothing v; k(VCode(TEApp fun arg))}
app tag nonfun x k = fail ("A nonfunction ("++show nonfun++") in function position.\nArising from the operator "++tag)


-- ???: what is 'C'?
evalC:: TExpr -> VEnv -> (Value IO -> IO a) -> IO a
evalC exp env k =   -- println ("Entering eval: "++ show exp) >> 
                    heval exp env k where 
  heval:: TExpr -> VEnv -> (Value IO -> IO a) -> IO a                    
  heval (TELit loc x) env k = k(VBase loc x)
  heval (TEVar nm sch) env k = 
     do { (uniq,v) <- evalMVar (rtbindings env) nm (rtbindings env); k v}
  heval (TECon mu c rho arity xs) env k = evalList [] xs env k 
    where evalList vs [] env k = k(VCon mu arity (name c) (reverse vs))
          evalList vs (x:xs) env k = 
             evalC x env (\ v -> evalList (v:vs) xs env k)  
  heval (TEApp f x) env k = 
     evalC f env (\ v1 -> evalC x env (\ v2 -> apply f x v1 v2 k))
  heval (TEAbs elim ms) env k = do { i <- nextinteger; k(VFunM i (trymatching elim env ms ms))}
  heval (TETuple xs) env k = evalList [] xs env k
    where evalList vs [] env k = k(VTuple (reverse vs))
          evalList vs (x:xs) env k = 
             evalC x env (\ v -> evalList (v:vs) xs env k)
  heval (TEIn kind x) env k = heval x env (k . (VIn kind))
  heval (AppTyp e t) env k = heval e env k
  heval (AbsTyp t e) env k = heval e env k
  heval (TECast p e) env k = heval e env k
  heval (t@(Emv _)) env k = k (VCode t) -- fail ("Evaluating mutvar: "++show t)
  heval (CSP(nm,i,v)) env k = k v                
  heval (exp@(TEMend tag elim x ms)) env k 
      | Just numpats <- sameLenClauses2 (near x++tag) ms
      = do { phi <- unwind exp env numpats [] return
           ; arg <- evalC x env return
           ; case (tag) of
              ("mcata") -> phiHas1Arg exp env phi arg k 
              ("mhist") -> phiHas2Arg exp env phi arg (VFun whoknows outf) k
                 where outf (VIn k x) = x
                       outf v = error ("abstract out applied to non Mu type: "++show v)
              ("mprim") -> phiHas2Arg exp env phi arg (VFun whoknows id) k             
              ("msfcata") -> phiHas2Arg exp env phi arg (VFun whoknows inversef) k
                 where inversef x = (VInverse x)
              (x) -> fail ("Unimplemented mendler operator: "++x)
              }



phiHas1Arg :: forall b . TExpr -> VEnv -> Value IO -> Value IO -> (Value IO -> IO b) -> IO b
phiHas1Arg (TEMend tag elim _ ms) env phi argv k = 
   do { i <- nextinteger
      -- f is the recursive caller (mcata phi)
      --  mcata phi (VIn x) = phi (mcata phi) x
      ; let f:: forall b . Value IO -> (Value IO -> IO b) -> IO b
            f (VIn kind x) k = do { v <- app "mcata" phi (VFunM i f) return
                                  ; app "mcata" v x k}
            f (VCode e) k = 
                 do { ms2 <- mapM (normClause env) ms
                    ; k(VCode(TEMend tag elim e ms2)) }
            f v k = fail ("mcata applied to non Mu type value: "++show v++" "++show i++"\n"++
                         (plistf (\(_,x,y) -> show x++":"++show y) "\n  " ms "\n  " ""))
      ; app tag (VFunM i f) argv k }   
      
phiHas2Arg
  :: TExpr               -- source code
     -> VEnv             -- dynamic environment
     -> Value IO         -- the phi function
     -> Value IO         -- value to be analyzed
     -> Value IO         -- the second argument (after the recursive caller) of phi
     -> (Value IO -> IO b) -- the current continuation
     -> IO b
phiHas2Arg (TEMend tag elim _ ms) env phi arg1 arg2 k = 
   do { i <- nextinteger
      ; let f:: forall b . Value IO -> (Value IO -> IO b) -> IO b
            f (VIn kind x) k = do { v <- app tag phi (VFunM i f) return
                                  ; u <- app tag v arg2 return
                                  ; app tag u x k}
            f (VInverse x) k | tag == "msfcata" = k x
            f (VCode e) k = 
                 do { ms2 <- mapM (normClause env) ms
                    ; k(VCode(TEMend tag elim e ms2)) }            
            f v k = fail (tag++" applied to non Mu type: "++show v)
      ; app tag (VFunM i f) arg1 k}  

-- Turn a list of Clauses (the phi function has n args) into a function with continuation 
unwind:: TExpr -> VEnv -> Int -> [Value IO] -> (Value IO -> IO b) -> IO b
unwind (term@(TEMend tag elim x cls)) env 0 vs k = tryClauses term cls2 env (reverse vs) cls2 k
  where proj(tele,ps,e) = (ps,e)
        cls2 = (map proj cls)
unwind cls env n vs k = 
    do { i <- nextinteger; k (VFunM i (\ v k1 -> unwind cls env (n-1) (v:vs) k1)) }


trymatching elim env ms [] v k = fail ("No pattern matches "++show v++"\n   "++show ms)
trymatching elim env ms ((pat,exp):more) (v@(VCode codeExp)) k = 
   do { let g (p,e) = do { (_,[p2],e2) <- normClause env (0,[p],e)
                          ; return(p2,e2) }
      ; normcls <- mapM g ms
      ; k(VCode (TEApp (TEAbs elim normcls) codeExp)) }      
trymatching elim env ms ((pat,exp):more) v k =
            maybe (trymatching elim env ms more v k)   
                  (\ env2 -> evalC exp env2 k)
              =<< matchM env pat v

-- try each clause, matching the patterns agianst the values   
tryClauses:: TExpr -> [([Pat], TExpr)]  -> VEnv -> [Value IO] -> [([Pat], TExpr)] -> (Value IO -> IO b) -> IO b
tryClauses efun allcls env2 vs [] k = fail ("No clause matches the inputs: "++plistf show "" vs " " ""++plistf g "\n  " allcls "\n  " "\n")
   where g (ps,e) = plistf show "" ps " " "-> " ++ show e
tryClauses efun allcls env2 vs ((ps,e):more) k = 
   do { menv <- matchPatsToVals efun env2 ps vs
      ; case menv of
         NoMatch -> tryClauses efun allcls env2 vs more k
         AllPatsMatch env3 -> evalC e env3 k 
         NeutralTerm ->  -- f p1 p2 = e1
                         -- f q1 q2 = e2
                         -- 
                         -- f 5 <e> --> (\ (p1,p2) -> e1; (q1,q2) -> e2) (5,e)
           do { argv <- reify 0 (VTuple vs)
              ; let g (ps,e) = do { (_,ps2,e2) <- normClause env2 (0,ps,e)
                                  ; return(PTuple ps2,e2) }
              ; normcls <- mapM g allcls
              ; k(VCode (TEApp (TEAbs ElimConst normcls) argv)) } }
            

data ClauseCase env = AllPatsMatch env | NoMatch | NeutralTerm

matchPatsToVals :: TExpr -> VEnv -> [Pat] -> [Value IO] -> IO(ClauseCase VEnv)
matchPatsToVals efun env [] [] = return(AllPatsMatch env)
matchPatsToVals efun env (p:ps) ((v@(VCode e)): vs) | refutable p = return NeutralTerm
  where refutable (PVar _ _) = False
        refutable (PWild pos) = False
        refutable p = True
matchPatsToVals efun env (p:ps) (v:vs) = 
  do { menv <- matchM env p v
     ; maybe (return NoMatch) 
             (\ env2 -> matchPatsToVals efun env2 ps vs)
             menv }
             
expEnvWithPatMatchingFun:: Int -> Name -> [([Pat], TExpr)] -> VEnv -> IO (VEnv)
expEnvWithPatMatchingFun numPatInClauses nm cls env = 
   do { uniq <- nextinteger
      ; vfun <- fixIO (\ v -> unwind2 (CSP(nm,uniq,v)) cls env numPatInClauses [] return)
      ; return((extendEnvName [(nm,uniq,vfun)] env))}
      
     
unwind2:: TExpr -> [([Pat], TExpr)] -> VEnv -> Int -> [Value IO] -> (Value IO -> IO b) -> IO b
unwind2 efun cls env 0 vs k = tryClauses efun cls env (reverse vs) cls k
unwind2 efun cls env n vs k = 
   do { i <- nextinteger; k (VFunM i (\ v k1 -> unwind2 efun cls env (n-1) (v:vs) k1))}
                  

-------------------------------------------------------------------
-- refifcation
-------------------------------------------------------------------

-- To reify we have to normalize clauses
normClause env (tele,ps,exp) =
  do { (ps2,delta) <- threadFresh id ps [] []
     ; v <- evalC exp (extendEnvName delta env) return
     ; exp2 <- reify 0 v
     ; return(tele,ps2,exp2)
     }
threadFresh f [] qs ans = return(f (reverse qs),ans)
threadFresh f (p:ps) qs ans =
   do { (q,ans2) <- freshPat (p,ans); threadFresh f ps (q:qs) ans2 }
   
freshPat:: (Pat,[(Name, Integer, Value IO)]) -> 
           IO (Pat,[(Name, Integer, Value IO)])
freshPat (pat,ans) = 
     case pat of
      PLit pos l -> return(pat,ans)
      PWild pos -> return(pat,ans)
      PTuple ps -> threadFresh PTuple ps [] ans
      PCon nm ps -> threadFresh (PCon nm) ps [] ans
      PVar nm mt -> 
        do { nm2 <- freshNameIO nm
           ; i <- nextinteger
           ; let sch Nothing = undefined
                 sch (Just t) = Sch [] (Tau t)
           ; return(PVar nm2 mt,(nm,i,VCode(TEVar nm2 (sch mt))):ans)}      

reify  n x  = help n x  where
  help n (VBase pos x) = return (TELit noPos x)
  help n (VFun ty f) = 
   do { next <- nextinteger
      ; let name = Nm("%"++show next,noPos)
      ; let result = f (VCode (TEVar name (Sch [] (Tau ty))))
      ; body <- reify n result
      ; return(TEAbs ElimConst [(PVar name (Just ty),body)])}
  help n (VFunM i f) =
   do { next <- nextinteger
      ; let name = Nm("%"++show next,noPos)
      ; result <- f (VCode (TEVar name (error "type of var in reify"))) return
      ; body <- reify n result
      ; return(TEAbs (ElimConst) [(PVar name Nothing,body)])}
  help n (VTuple xs) = liftM TETuple (mapM (reify n) xs)
  help n (VCon mu arity c vs) = liftM econ (mapM (reify n) vs)
   where econ es = TECon mu (toName c) (Tau tunit) arity es
        -- applyTE ( CSP(toName c,mu,VCon mu arity c []) : es)

  help n (VIn kind x) = liftM (TEIn kind) (reify n x)
  help n (VInverse v) = error ("No VInverse in reify yet: "++show v)
  help n (VCode e) = return e
  help n (VProof t1 t2) = error ("No VProof in reify yet: "++show t1++"="++show t2)
  help n (VType t) =  error ("No VType in reify yet: "++show t)

-- Normaliztion works for closed terms, where functions have been
-- replaced with their CSP constants

normform :: TExpr -> FIO TExpr 
normform x = fio (evalC x closedEnv (reify 0))
  where closedEnv = VEnv [] []

-------------------------------------------------------------------
-- evaluating declarations extends the environment

evalDecC :: VEnv -> Decl TExpr -> (VEnv -> IO a) -> IO a 
evalDecC env (d@(Axiom p nm t)) k = 
    k (env{ctbindings = (nm,Type t):(ctbindings env)
          ,rtbindings = (nm,-675,error("Call to Axiom "++show nm)):(rtbindings env)})
evalDecC env (d@(Def _ pat exp)) k = 
   -- println ("\n\nDefining: "++show d++"\nIn environment\n"++ browse (Just 10) env) >>
   evalC exp env ((maybe (fail "no Match") k =<<) . matchM env pat)
evalDecC env (DataDec pos t args cs derivs) k = k env
{-
   do { let acc env (c,argtyps) = 
                 do { mu <- case conkeyM (name c) of { Just n -> return n; Nothing -> return }
                    ; return ((c,i,VCon mu (length cs) (name c) []):env) }                 
      ; env2 <- (foldM acc [] cs)
      ; k(extendEnvName env2 env) }
-}
evalDecC env (FunDec pos nm ts cls) k | Just n <- sameLenClauses nm cls = 
     do { env2 <- expEnvWithPatMatchingFun n (Nm(nm,pos)) cls env; k env2 }
evalDecC env (FunDec pos nm ts cls) k = fail (show pos++"\nFunction: "++nm++", has varying number of arguments.")   
evalDecC env (GADT pos t kind cs derivs) k = k env
{-
   do { let acc env (c,free,doms,range) = 
                 do { i <- case conkeyM (name c) of { Just n -> return n; Nothing -> nextinteger}
                    ; return ((c,i,VCon i (length cs) (name c) []):env)}                 
      ; env2 <- (foldM acc [] cs)
      ; k(extendEnvName env2 env) }
-}      
evalDecC env (Synonym pos nm xs body) k = k env      
  

sameLenClauses2 nm [] = error ("Function with no body: "++show nm)
sameLenClauses2 nm [(_,ps,e)] = Just (length ps)
sameLenClauses2 nm ((_,ps,e):more) = 
      if length ps == m
         then Just m
         else error ("Function "++show nm++" has different arities.")
    where (Just m) = sameLenClauses2 nm more
    
sameLenClauses nm [] = error ("Function with no body: "++show nm)
sameLenClauses nm [(ps,e)] = Just (length ps)
sameLenClauses nm ((ps,e):more) = 
      if length ps == m
         then Just m
         else error ("Function "++show nm++" has different arities.")
    where (Just m) = sameLenClauses nm more    

evalIO :: TExpr -> VEnv -> IO (Value IO)
evalIO exp env = evalC exp env return

------------------------------------------------------------

