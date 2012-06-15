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
import Monads(FIO,fio)
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
  
trymatching env ms [] v k = fail ("No pattern matches "++show v++"\n   "++show ms)
-- trymatching env ms ((pat,exp):more) (v@(VCode e)) k = 
     -- at PatVar would be OK here -- error ("Try matching sees a code value: "++show v)
trymatching env ms ((pat,exp):more) v k =
            maybe (trymatching env ms more v k)   
                  (\ env2 -> evalC exp env2 k)
              =<< matchM env pat v

matchM:: VEnv -> Pat -> Value IO -> IO(Maybe (VEnv))
matchM env p v = 
     case (match [] p v) of
       Just pairs -> do { us <- mapM new pairs; return(Just (extendEnvName us env))}
       Nothing -> return Nothing
  where new (nm,v) = do { u <- nextinteger; return(nm,u,v)}


----------------------------------------------------
apply:: TExpr -> TExpr -> Value IO -> Value IO -> (Value IO -> IO a) -> IO a
apply g y fun arg k = 
        -- println("\napply: ("++show (EApp g [y])++"). "++show fun++" "++show arg) >>
        help fun arg k where
   help (VFunM n vf) x k = vf x k
   help (VFun ty g) x k = k(g x)
   help (VCon i arity c vs) v k | arity > length vs = k(VCon i arity c (vs ++ [v]))
   help (VCode fun) v k = do { putStrLn ("THERE "++show fun); arg <- reify Nothing v; k(VCode(TEApp fun arg))}
   help nonfun x k = fail ( near g ++ "A nonfunction ("++show nonfun++") in function position.\nArising from the term\n "++show(TEApp g y))

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
  heval (TEAbs elim ms) env k = do { i <- nextinteger; k(VFunM i (trymatching env ms ms))}
        --             mkFun i  k }          
 -- mkFun n f k = k(VFunM n f)
  heval (TETuple xs) env k = evalList [] xs env k
    where evalList vs [] env k = k(VTuple (reverse vs))
          evalList vs (x:xs) env k = 
             evalC x env (\ v -> evalList (v:vs) xs env k)
  heval (TEIn kind x) env k = heval x env (k . (VIn kind))
  heval (AppTyp e t) env k = heval e env k
  heval (AbsTyp t e) env k = heval e env k
  heval (TECast p e) env k = heval e env k
  heval (t@(Emv _)) env k = k (VCode t) -- fail ("Evaluating mutvar: "++show t)
  heval (TEMend tag elim x ms) env k 
      | Just numpats <- sameLenClauses2 (near x++tag) ms
      = do { phi <- unwind ms env numpats [] return
           ; arg <- evalC x env return
           ; case (arg,tag) of
              (VCode e,_) -> error("\nBad arg to Mendler "++show e)
              (_,"mcata")   -> mcata (plistf (\(_,x,y) -> show x++":"++show y) "\n  " ms "\n  " "") phi (\ f -> app "mcata" f arg k)
              (_,"mhist")   -> mhist   phi (\ f -> app "mhist" f arg k)  
              (_,"mprim")   -> mprim   phi (\ f -> app "mprim" f arg k)
              (_,"msfcata") -> msfcata phi (\ f -> app "msfcata" f arg k)
              (_,"msfprim") -> msfprim phi (\ f -> app "msfprim" f arg k)
              (_,x) -> fail ("Unimplemented mendler operator: "++x)
              }
  heval (CSP(nm,i,v)) env k = k v              

unwind:: [(Telescope,[Pat], TExpr)] -> VEnv -> Int -> [Value IO] -> (Value IO -> IO b) -> IO b
unwind cls env 0 vs k = tryClauses (error "NO TERM for unwind") cls2 env (reverse vs) cls2 k
  where proj(tele,ps,e) = (ps,e)
        cls2 = (map proj cls)
unwind cls env n vs k = 
    do { i <- nextinteger; k (VFunM i (\ v k1 -> unwind cls env (n-1) (v:vs) k1)) }
   

unwind2:: TExpr -> [([Pat], TExpr)] -> VEnv -> Int -> [Value IO] -> (Value IO -> IO b) -> IO b
unwind2 efun cls env 0 vs k = tryClauses efun cls env (reverse vs) cls k
unwind2 efun cls env n vs k = 
   do { i <- nextinteger; k (VFunM i (\ v k1 -> unwind2 efun cls env (n-1) (v:vs) k1))}

   

app tag (VFunM n vf) x k = vf x k
app tag (VFun ty g) x k = k(g x)
app tag (VCon i arity c vs) v k | arity > length vs = k(VCon i arity c (vs ++ [v]))
app tag (VCode fun) v k = do { putStrLn ("HERE "++show fun); arg <- reify Nothing v; k(VCode(TEApp fun arg))}
app tag nonfun x k = fail ("A nonfunction ("++show nonfun++") in function position.\nArising from the operator "++tag)


--  mcata phi (VIn x) = phi (mcata phi) x
mcata :: forall b . String -> Value IO -> (Value IO -> IO b) -> IO b
mcata ms phi k = 
   do { i <- nextinteger
--      ; putStrLn("\nMCATA "++show i)
      ; let f:: forall b . Value IO -> (Value IO -> IO b) -> IO b
            f (VIn kind x) k = do { v <- app "mcata" phi (VFunM i f) return
                                  ; app "mcata" v x k}
{-
--- What if its code? like this?

            f (VCode e) k = do { v <- app "mcata" phi (VFunM i f) return
                               ; app "mcata" v (VCode e) k}
-}                               
                               
            f v k = fail ("mcata applied to non Mu type value: "++show v++" "++show i++"\n"++ms)
      ; k(VFunM i f)}   
      
mplus :: forall b . Value IO -> String -> Value IO -> (Value IO -> IO b) -> IO b
mplus arg2 tag phi k = 
   do { i <- nextinteger
      ; let f:: forall b . Value IO -> (Value IO -> IO b) -> IO b
            f (VIn kind x) k = do { v <- app tag phi (VFunM i f) return
                                  ; u <- app tag v arg2 return
                                  ; app tag u x k}
            f (VInverse x) k | tag == "msfcata" = k x
            f v k = fail (tag++" applied to non Mu type: "++show v)
      ; k(VFunM i f)}        

-- mhist phi (In x) = phi (mhist phi) out x
mhist phi k = mplus (VFun whoknows outf) "mhist" phi k
  where outf (VIn k x) = x
        outf v = error ("abstract out applied to non Mu type: "++show v)

-- msfcata phi (VIn x) = phi (msfcata phi) VInverse x
-- msfcata phi (VInverse x) = x
msfcata phi k = mplus (VFun whoknows inversef) "msfcata" phi k
  where inversef x = (VInverse x)
  
msfprim phi k = 
   do { i <- nextinteger
      ; let f:: forall b . Value IO -> (Value IO -> IO b) -> IO b
            f (VIn kind x) k = do { v <- app tag phi (VFun whoknows VInverse) return
                                  ; u <- app tag v (VFun whoknows id) return
                                  ; app tag u x k}
            f (VInverse x) k = k x
            f v k = fail (tag++" applied to non Mu type: "++show v)
      ; k(VFunM i f)}  
 where tag = "msfprim"      
  
-- mprim phi (VIn x) = phi (msfcata phi) id x
mprim phi k = mplus (VFun whoknows id) "mprim" phi k
  
           

-------------------------------------------------------------------
-- evaluating declarations extends the environment

evalDecC :: VEnv -> Decl TExpr -> (VEnv -> IO a) -> IO a 
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


expEnvWithPatMatchingFun:: Int -> Name -> [([Pat], TExpr)] -> VEnv -> IO (VEnv)
expEnvWithPatMatchingFun numPatInClauses nm cls env = 
   do { uniq <- nextinteger
      ; vfun <- fixIO (\ v -> unwind2 (CSP(nm,uniq,v)) cls env numPatInClauses [] return)
      ; return((extendEnvName [(nm,uniq,vfun)] env))}



tryClauses:: TExpr -> [([Pat], TExpr)]  -> VEnv -> [Value IO] -> [([Pat], TExpr)] -> (Value IO -> IO b) -> IO b
tryClauses efun allcls env2 vs [] k = fail ("No clause matches the inputs: "++plistf show "" vs " " ""++plistf g "\n  " allcls "\n  " "\n")
   where g (ps,e) = plistf show "" ps " " "-> " ++ show e
tryClauses efun allcls env2 vs ((ps,e):more) k = -- putStrLn ("TRY CLAUSES "++show vs++ show ps) >>
   maybe (tryClauses efun allcls env2 vs more k)  
         (\ env3 -> evalC e env3 k)
     =<< threadC efun env2 ps vs
          
threadC :: TExpr -> VEnv -> [Pat] -> [Value IO] -> IO(Maybe (VEnv))
threadC efun env [] [] = return(Just env)
threadC efun env (p:ps) (v:vs) = 
  maybe n
        (\ env2 -> threadC efun env2 ps vs)
    =<< matchM env p v
 where
  n = case v of
        (VCode e) -> fail ("Code value in threadC: "++ show (TEApp efun e))
        _ -> return Nothing

evalIO :: TExpr -> VEnv -> IO (Value IO)
evalIO exp env = evalC exp env return

------------------------------------------------------------

reify  n x  = help n x  where
  help n (VBase pos x) = return (TELit noPos x)
  help n (VFun ty f) = 
   do { next <- nextinteger
      ; let name = Nm("%"++show next,noPos)
      ; let result = f (VCode (TEVar name (Sch [] (Tau ty))))
      ; body <- reify n result
      ; return(TEAbs undefined [(PVar name (Just ty),body)])}
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
