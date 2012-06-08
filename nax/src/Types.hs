{-# LANGUAGE TupleSections #-}

module Types where

-- Get the FIO monad
import Monads

-- Useful functions over monads and lists
import Data.List(union,unionBy,any,(\\),partition)
import Data.Char(isUpper)
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import Control.Monad (foldM,liftM,liftM2,liftM3)

-- These are for pretty printing
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)
import Names
import BaseTypes
import Syntax
import Eval(normform)
 
import Debug.Trace 
----------------------------------------------------------------
-- Matching a Typ with another, used in Synonyms


varClass (s,TyLift _)  = "expession variable "++show s
varClass (s,_) = "type variable "++show s



add:: (Name,Typ) -> [(Name,Typ)] -> Maybe [(Name,Typ)] 
add (n,typ) [] = Just[(n,typ)] 
add (n,typ) (vs@((m,x):more)) | n==m =
   if typ==x then Just vs else Nothing
add (n,typ) ((m,x):more) | n==m = error ("Class doesn't match, "++varClass (n,typ)++" used as "++varClass (m,x)++".")
add p (q:more) = do { qs <- add p more; return (q:qs)}
  
matchT:: [Name] -> (Typ,Typ) -> [(Name,Typ)] -> Maybe [(Name,Typ)] 
matchT vars (pat,typ) env = 
  case (pat,typ) of
    (TyVar n _,typ) | elem n vars -> add (n,typ) env
    (TyVar n _, TyVar m _) | n==m -> return env
    (TyApp x y,TyApp m n) -> 
       do { env2 <- matchT vars (x,m) env; matchT vars (y,n) env2}
    (TyTuple _ xs,TyTuple _ ys) | length xs==length ys ->
       foldM (flip $ matchT vars) env (zip xs ys)
    (TyCon _ n _,TyCon _ m _) | n==m -> return env   
    (TyProof x y,TyProof m n) -> 
       do { env2 <- matchT vars (x,m) env; matchT vars (y,n) env2}
    (TyArr x y,TyArr m n) -> 
       do { env2 <- matchT vars (x,m) env; matchT vars (y,n) env2}  
    (TySyn nm arity xs x,y) -> matchT vars (x,y) env
    (y,TySyn nm arity xs x) -> matchT vars (y,x) env
    (TyMu k1,TyMu k2) -> matchK vars (k1,k2) env
    (TcTv(u1,p1,k1),TcTv(u2,p2,k2)) | u1==u2 -> return env
    (TyLift (Checked e1),TyLift (Checked e2)) -> matchE vars (e1,e2) env
    (TyAll vs t,TyAll ys s) -> error ("No TyAll in matchT yet")
    (_,_) -> Nothing

matchK:: [Name] -> (Kind,Kind) -> [(Name,Typ)] -> Maybe [(Name,Typ)] 
matchK vars (pat,kind) env = 
  case (pat,kind) of
    (Kname n,LiftK typ) | elem n vars -> add (n,typ) env
    (Kname n, Kname m ) | n==m -> return env   
    (Kname n,k) -> fail ("Kind var "++show n++" in matchK")    
    (Star,Star) -> return env
    (LiftK t1,LiftK t2) -> matchT vars (t1,t2) env
    (Karr x y,Karr m n) -> 
       do { env2 <- matchK vars (x,m) env; matchK vars (y,n) env2}
    (Kvar(u1,p1),Kvar(u2,p2)) | u1==u2 -> return env  
    (_,_) -> Nothing
    
    
matchE:: [Name] -> (TExpr,TExpr) -> [(Name,Typ)] -> Maybe [(Name,Typ)] 
matchE vars (pat,exp) env = 
  case (pat,exp) of
    (TEVar n _, e) | elem n vars -> add (n,TyLift (Checked e)) env
    (TELit _ x,TELit _ y) | x==y -> return env
    (TEVar n _,TEVar m _) | n==m -> return env    
    (TEApp x y,TEApp m n) -> 
       do { env2 <- matchE vars (x,m) env; matchE vars (y,n) env2}  
    (TEAbs _ _,TEAbs _ _) -> error ("No TEAbs in matchE yet: "++show pat++" =?= "++show exp)
    (TECon _ c1 _ a1 xs1,TECon _ c2 _ a2 xs2) | c1==c2 && a1==a2 
       ->  foldM (flip $ matchE vars) env (zip xs1 xs2) 
    (TETuple xs,TETuple ys) | length xs==length ys ->
       foldM (flip $ matchE vars) env (zip xs ys) 
    (TELet _ _,TELet _ _) -> error ("No TELet in matchE yet: "++show pat++" =?= "++show exp)
    (TEIn k1 x,TEIn k2 y) ->
       do { env2 <- matchE vars (x,y) env; matchK vars (k1,k2) env2} 
    (TECast p x,y) -> matchE vars (x,y) env
    (x,TECast p y) -> matchE vars (x,y) env
    (TEMend _ _ _ _,TEMend _ _ _ _) -> error ("No TEMend in matchE yet: "++show pat++" =?= "++show exp)
    (AppTyp _ _,AppTyp _ _) -> error ("No AppTyp in matchE yet: "++show pat++" =?= "++show exp)    
    (AbsTyp _ _,AbsTyp _ _) -> error ("No AbsTyp in matchE yet: "++show pat++" =?= "++show exp)    
    (Emv(u1,p1,k1),Emv(u2,p2,k2)) | u1==u2 -> return env
    (CSP(u1,p1,k1),CSP(u2,p2,k2)) | u1==u2 -> return env  
    (_,_) -> Nothing
    

synonymPrint :: Name -> [Name] -> Typ -> Typ -> Maybe Typ    
synonymPrint name vars pat term = 
  case matchT vars (pat,term) [] of
    Just xs -> Just(applyT(TyVar name Star : map snd (orderK vars xs)))
    Nothing -> Nothing


synonymExpand:: Name -> [Class Name Name Name] -> PolyKind -> Typ ->
                (Int,Name -> [(Typ,Kind)]-> FIO Typ)
synonymExpand nm xs polyk body = (length xs,f nm xs polyk body)
  where f synName formals polyk body nm actuals = 
           do { kind <- instanK (loc synName) polyk
              -- ; writeln("\nFormals = "++show formals++"\nActuals = "++show actuals)
              ; zs <- match actuals formals kind
              ; body2 <- tySubb (loc nm) ([],zs,[]) body
              -- ; writeln("\n body = "++show body2)
              ; zonk(TySyn nm (length formals) (map fst actuals) body2) }
        match [] [] k = return []
        match ((t1,k1):more) (n:ns) (Karr k2 k3) = 
           do { unifyK (loc t1) ["Checking the kind of the actual arg '"++show t1++
                                 "' in the "++show nm++" synonym application."] k1 k2
              ; zs <- match more ns k3
               ; return(toSub t1 n : zs) }
        match xs ys k = fail("\nError *****\nBad type synonym application.\n  "++show xs++"\n  "++show ys++"\n  "++show k)
        toSub :: Typ -> Class Name Name Name -> (Name,Class Kind Typ TExpr)
        toSub t (Kind n) = error ""
        toSub (TyLift (Checked e)) (Exp n) = (n,Exp e)
        toSub t (Type n) = (n,Type t)
              
              
  

orderK [] xs = []
orderK (nm:names) xs = find xs : orderK names xs
  where find [] = error ("Synonym var not matched: "++show nm)
        find ((m,t):more) | nm==m = (m,t)
        find (m : more) = find more        
       
       
     

-------------------------------------------------------    

-- tupleTypes (TyApp (TyApp (TyCon _ "(,)" _) x) y) = x : tupleTypes y
tupleTypes (TyTuple k xs) = xs
tupleTypes x = [x]


-----------------------------------------------
-- operations on Typ

freshType k = 
  do { n <- fio(nextInteger)
     ; p <- fio(newIORef Nothing)
     ; return(TcTv (n,p,k)) }

freshRho k = do { t <- freshType k; return(Tau t)}
freshScheme k = do { r <- freshRho k; return(Sch [] r)}
     
     
prune :: Typ -> FIO Typ
prune (typ @ (TcTv (uniq,ref,k))) =
  do { maybet <- fio(readIORef ref)
     ; case maybet of
         Nothing -> return typ
         Just t -> do{t2 <- prune t; fio(writeIORef ref (Just t2)); return t2}}
prune t = return t

getTyVars:: Typ -> [(Name,Kind)] 
getTyVars (TyVar n k) = [(n,k)]
getTyVars (TyCon _ s k) = []
getTyVars (TyTuple k xs) = foldr acc [] xs
  where acc t ans = unionBy eq (getTyVars t) ans where eq (p1,k1) (p2,k2) = p1==p2
getTyVars (TyApp x y) = unionBy eq (getTyVars x) (getTyVars y) where eq (p1,k1) (p2,k2) = p1==p2
getTyVars (TcTv (uniq,ptr,k)) = []          

------------------------------------------------------------

freshExp :: Typ -> FIO (TExpr)
freshExp t = 
  do { n <- fio(nextInteger)
     ; p <- fio(newIORef Nothing)
     ; return(Emv (n,p,t)) }
    
pruneE :: TExpr -> FIO (TExpr)
pruneE (typ @ (Emv (uniq,ref,k))) =
  do { maybet <- fio(readIORef ref)
     ; case maybet of
         Nothing -> return typ
         Just t -> do{t2 <- pruneE t; fio(writeIORef ref (Just t2)); return t2}}
pruneE t = return t


-----------------------------------------------------------------------

unifyExp:: SourcePos -> [String] -> TExpr -> TExpr -> FIO ()
unifyExp loc mess t1 t2 = do { unifyExpT loc mess t1 t1; return ()}

unifyLT f t1 t2 loc m ps [] [] = return(f(reverse ps))
unifyLT f t1 t2 loc m ps (x:xs) (y:ys) = 
   do { p <- unifyExpT loc m x y; unifyLT f t1 t2 loc m (p:ps) xs ys}
unifyLT f t1 t2 loc m ps xs ys = matchErr loc ("different lengths": m) t1 t2

unifyExpT:: SourcePos -> [String] -> TExpr -> TExpr -> FIO TExpr
unifyExpT loc message x y = do { x1 <- pruneE x; y1 <- pruneE y; f x1 y1 }
 where f (exp@(TELit p x)) (TELit _ y) | x==y = return exp
       f (exp@(TEVar(Nm(x,_)) sch)) (TEVar(Nm(y,_)) sch2) | x==y = return exp
       f (TEApp x y) (TEApp a b) = 
          do { x1 <- unifyExpT loc message x a
             ; x2 <- unifyExpT loc message y b
             ; return(TEApp x1 x2) }
       f (TEAbs e1 _) (TEAbs e2 _) = error "No Abs in unifyExp yet."
       f (z@(TECon mu c rho a xs)) (w@(TECon _ d _ b ys)) 
              | c==d && a==b 
              = unifyLT (TECon mu c rho a) z w loc message [] xs ys          
       f (x@(TETuple xs)) (y@(TETuple ys)) = unifyLT TETuple x y loc message [] xs ys
       f (TELet x y) (TELet m n) = error "No Let in instance (Eq Expr) yet."
       f (TEIn k1 x) (TEIn k2 y) = 
          do { unifyK loc message k1 k2
             ; p <- unifyExpT loc message x y
             ; return(TEIn k1 p) }
       f (TEMend tag elim arg ms) (TEMend _ _ _ _) = error "No EMend in instance (Eq Expr) yet."
       f (AppTyp x ts) (AppTyp y ss) =
          do { unifyL Star loc message ts ss
             ; p <- unifyExpT loc message x y
             ; return(AppTyp p ts)}
       f (exp@(AbsTyp x y)) (AbsTyp a b) = error "No ETyAbs in instance (Eq Expr) yet."
       f (exp@(TECast p x)) y = unifyExpT loc message x y
       f (exp@(x)) (TECast p y) = unifyExpT loc message x y   
       f (exp@(ContextHole x y)) z = error ("Can't unify context hole")
       f z (ContextHole x y) = error ("Can't unify context hole")       
       f (exp@(Emv(u1,r1,k1))) (Emv(u2,r2,k2)) | r1==r2 = return exp
       f (Emv x) t = unifyExpVar loc message x t >> return t
       f t (Emv x) = unifyExpVar loc message x t >> return t
       f (exp@(CSP (nm,i,u))) (CSP (n,j,v)) | i==j = return exp
       f s t = do { s2 <- zonkExp s
                  ; t2 <- zonkExp t
                  ; let trans msg =
                          "While comparing the normal forms of\n   "
                          ++show s2++"\nand\n   "++show t2++"\n"++msg
                  ; handleM (compareTerms loc message s2 t2) trans
                  ; return(ContextHole s2 t2)}
                 

compareTerms loc message x y =
  do { xnf <- normform x
     ; ynf <- normform y
--     ; writeln("\nStarting terms "++show x++" =?= "++show y)
--     ; writeln("Normal forms   "++show xnf++" =?= "++show ynf)
     ; if xnf == ynf
          then return ()
          else  matchErr loc 
                (("Term unification fails\n   "++
                  show xnf++ " =/= " ++show ynf):
                  message)  x y }

unifyExpVar loc message (x@(u1,r1,typ)) term =
  do { (ptrs,names) <- getVarsExpr term
     ; let same (Exp(u0,r0,k0)) = r0==r1
           same _ = False
    --  ; writeln("Unifying var "++show (Emv x)++" and "++show term)
    
     ; if (any same ptrs) 
          then do { term2 <- zonkExp term
                  ; tnf <- normform term2
                  ; (matchErr loc (("\nExp Occurs check\n "++show (Emv x)++
                        " in ("++show term2++") with vars "++show ptrs++
                        "\nnormal form = "++show tnf++"\n"++show term): message)  (Emv x) term2) }
          else return ()
              
    {-
     ; rho <- checkExp term
     ; case rho of
         Tau typ2 -> unify loc message typ2 typ
         Rarr sch dom -> fail (unlines(("Polymorphic type in unifyExpVar: "++show rho):message))
    -}
     ; fio(writeIORef r1 (Just term))
     ; return ()
     }

firstOrder loc message expect var term rho = 
    case rho of
      (Rarr _ _) -> fail (unlines(mR rho:message))
      (Tau t) ->  do { unify loc message expect t; x <- zonk t; check x }      
  where check (TyCon _ c k) = return ()
        check (TyApp f x) = check f
        check (TyMu k) = return ()
        check (TyTuple Star xs) = return ()
        check t = fail (unlines(m t : message))
        m t = "\n"++show loc++"\nAn expression variable: "++show var++", unifys to a term: "++
              (show term)++", that is not data: "++show t++"\n"++showT t
        mR t = "\n"++show loc++"\nAn expression variable: "++show var++", unifys to a term: "++
               (show term)++", that is not data: "++show t++"\n"++showR t              

unify :: SourcePos -> [String] -> Typ -> Typ -> FIO ()
unify loc message x y = do { x1 <- prune x; y1 <- prune y
                          --  ; writeln("\nUnify "++show x1++" =?= "++show y1)
                           ; f x1 y1 }
  where f (t1@(TyVar n k)) (t2@(TyVar n1 k1)) | n==n1 = return ()
        f (TyApp x y) (TyApp a b) = do { unify loc message x a; unify loc message y b }
        f (TyTuple k2 xs) (TyTuple k1 ys) | k1==k2  = unifyL k1 loc message xs ys
        f (x@(TyCon _ s _)) (y@(TyCon _ t _)) =
           if s==t then return () else matchErr loc ((show s++ " =/= " ++ show t++" (Different type constuctors)") : message) x y 
        f (TyProof x y) (TyProof a b) =
           do { unify loc message x a; unify loc message y b }
        f (TyArr x y) (TyArr a b) =
           do { unify loc message x a; unify loc message y b }   
        f (TySyn n1 a1 xs1 b1) x = unify loc message  b1 x
        f y (TySyn n2 a2 xs2 b2) = unify loc message y b2
        f (TyMu k1) (TyMu k2) = unifyK loc message k1 k2
        f (TcTv (u1,r1,k1)) (TcTv (u2,r2,k2)) | r1==r2 = return ()
        f (TcTv x) t = unifyVar loc message x t
        f t (TcTv x) = unifyVar loc message x t 
        f (TyLift (Checked e)) (TyLift (Checked g)) = 
            do { enf <- normform e
               ; gnf <- normform g
               ; writeln ("\nNormalizing "++show e++", "++show g)
               ; unifyExp loc message enf gnf }
        f (TyLift (Parsed e)) _ = error ("unchecked term in type inside unify: "++show e)
        f _ (TyLift (Parsed e)) = error ("unchecked term in type inside unify: "++show e)
--         f (TyLift (Pattern e)) _ = error ("unchecked term in type inside unify: "++show e)
--        f _ (TyLift (Pattern e)) = error ("unchecked term in type inside unify: "++show e)        
        f (TyAll vs t) (TyAll us s) = error ("No TyAll in unify yet")
        f s t = matchErr loc ((show s++ " =/= " ++show t++" (Different types)") : message)  s t


unifyL k loc m [] [] = return()
unifyL k loc m (x:xs) (y:ys) = unify loc m x y  >> unifyL k loc m xs ys
unifyL k loc m xs ys = matchErr loc ("different tuple lengths": m) (TyTuple k xs) (TyTuple k ys)

unifyVar loc message (x@(u1,r1,k)) t =
  do { (ptrs,names) <- getVars t
     ; let same (Type(u0,r0,k0)) = r0==r1
           same _ = False
     ; if (any same ptrs) 
          then (matchErr loc ("\nOccurs check" : message)  (TcTv x) t)
          else return ()
     ; check loc message t k 
     ; fio(writeIORef r1 (Just t))
     ; return ()
     }

------------
-- Checking that a type has a certain kind

kindOf:: Typ -> FIO Kind
kindOf t = do { x <- prune t; f x }
  where f (TyVar s k) = pruneK k
        f (TcTv (u,ptr,k)) = pruneK k
        f (TyTuple k ts) = pruneK k
        f (TyCon _ c k) = do { temp <- instanK noPos k
                             ; pruneK temp }
        f (TyProof _ _) = return Star
        f (TyArr _ _) = return(Karr Star (Karr Star Star))
        f (TySyn nm arity args body) = kindOf body
        f (TyMu k) = return (Karr (Karr k k) k)
        f (TyApp f x) = do { t2 <- kindOf f
                           ; case t2 of 
                               Karr x y -> return y
                               zz -> error("\nIn the type application: "++show t++"\n"++
                                           "the type constructor: "++show f++"\n"++
                                           "does not have an kind arrow as its sort: "++show t2)}
        f (TyLift (Checked e)) = liftM LiftK (typeOf e)
        f (TyLift e) = error ("No kindOf for lifted kinds over unchecked terms: "++show e)
        f (TyAll vs t) = kindOf t
        
check :: SourcePos -> [String] -> Typ -> Kind -> FIO ()
check loc message typ kind = -- writeln("\nCHECKING "++show typ++": "++show kind) >>
  case typ of
    TyVar s k -> unifyK loc (("Checking "++show s++"::"++show kind++".\nIt has kind "++show k++" instead.") : message) k kind
    TyApp f x -> 
      do { k1 <- freshKind  
         ; check loc message f (Karr k1 kind)
         ; check loc message x k1 }    
    TyArr x y -> 
      do { check loc message x Star
         ; check loc message y Star
         ; unifyK loc message kind Star
         }
    TyTuple knd xs -> 
      do { let f n Star = [Star | i <- [1..n]]
               f n (LiftK _) = fail "Non Star tuple"
               f 1 k = [k]
               f n k = fail ("Tuple kinds don't match in check")
         ; mapM (\ (t,k) -> check loc message t k) (zip xs (f (length xs) knd))
         ; unifyK loc (("Tuple has non-"++show knd++" kind"):message) kind knd
         }    
    TySyn nm arity xs body -> check loc message body kind         
    TyCon _ s polyk -> 
      do { k <- instanK loc polyk
         ; unifyK loc (("Checking type constructor "++show s++" with kind\n   "++show k++"\nhas expected kind:\n   "++show kind++"\n polykind = "++show polyk) : message) k kind }
    TyProof x y ->
      do { k1 <- freshKind
         ; check loc message x k1
         ; check loc message y k1
         ; let m = "Checking the proof "++show typ++" has kind *"
         ; unifyK loc (m:message) kind Star }
    TyMu k -> unifyK loc (m:message) kind (Karr (Karr k k) k)
      where m = "Checking (Mu "++show k++") has kind "++ show kind
    TyLift (Checked exp) -> 
      do { t1 <- typeOf exp
         ; unifyK loc (("Checking kind of lifted term: "++show exp++": "++
                        show t1++" =?= "++show kind):message) kind (LiftK t1) }
    TyLift e -> fail (unlines(("Unchecked term: "++show e++"in check"):message))                        
    TcTv (uniq,ptr,k) -> unifyK loc (("Checking t"++show uniq++" has kind "++ show kind) : message) k kind
    TyAll vs t -> check loc message t kind
    

checkRho:: SourcePos -> [String] -> Rho -> Kind -> FIO ()
checkRho loc m (Tau t) k = check loc m t k
checkRho loc m (Rarr s r) k = do { checkScheme loc m s Star; checkRho loc m r k}

checkScheme:: SourcePos -> [String] -> Scheme -> Kind -> FIO ()
checkScheme loc m (Sch vs r) k = checkRho loc m r k

-----------------------------------------------------
-- Zonking follows all mutable variable chains and eliminates them

zonkD:: Decl (TExpr) -> FIO (Decl TExpr)
zonkD (Def pos pat e) = liftM (Def pos pat) (zonkExp e)
zonkD (DataDec pos nm args cs derivs) = liftM (\ x -> DataDec pos nm args x derivs) (mapM f cs)
  where f (c,sch) = do { sch2 <- mapM zonkScheme sch; return(c,sch2)}
zonkD (GADT pos nm k cs derivs) = liftM2 (\ x y -> GADT pos nm x y derivs) (zonkKind k) (mapM f cs)
  where f (nm,args,doms,rng) = 
          do { doms2 <- mapM zonkScheme doms
             ; rng2 <- zonkRho rng
             ; return(nm,args,doms2,rng2)}
zonkD (FunDec pos fnm args cls) = liftM2 (FunDec pos fnm) (mapM f args) (mapM g cls)
  where f (nm,k) = do { k2 <- zonkKind k; return(nm,k2)}
        g (ps,e) = do { e2 <- zonkExp e; return(ps,e)}
zonkD (Synonym pos nm args typ) = 
  do { typ2 <- zonk typ; return(Synonym pos nm args typ)}
        
        
zonkE :: Expr -> FIO Expr
zonkE (ELit loc l) = return(ELit loc l)
zonkE (EVar nm) = return (EVar nm) 
zonkE (EFree nm) = return(EFree nm)
zonkE (ECon nm) = return (ECon nm)
zonkE (EApp x y) = liftM2 EApp (zonkE x) (zonkE y)
--zonkE (EAbs e1 ms) = liftM2 EAbs (zonkElim e1)(mapM g ms)
--            where g (p,e) = do { e2 <- zonkE e; return(p,e2)}
zonkE (ETuple es) = liftM ETuple (mapM zonkE es)
zonkE (EIn k x) = liftM2 EIn (zonkKind k)(zonkE x)
{-
zonkE (EMend tag elim scr ms) = liftM3 (TEMend tag) (zonkElim elim) (zonkExp scr) (mapM g ms)
            where g (ps,e) = do { e2 <- zonkExp e; return(ps,e2)}
-}

pruneTEqual (k @ (TVar(uniq,ref))) =
  do { maybet <- fio(readIORef ref)
     ; case maybet of
         Nothing -> return k
         Just k1 -> do{k2 <- pruneTEqual k1; fio(writeIORef ref (Just k2)); return k2}}
pruneTEqual t = return t

zonkPat:: Pat -> FIO Pat
zonkPat (PVar v (Just t)) = liftM (PVar v . Just) (zonk t)
zonkPat (PTuple ps) = liftM PTuple (mapM zonkPat ps)
zonkPat (PCon c ps) = liftM (PCon c) (mapM zonkPat ps)
zonkPat p = return p
             
zonkExp :: TExpr -> FIO TExpr
zonkExp x = do { y <- pruneE x; f y}
   where f (TELit loc l) = return(TELit loc l)
         f (TEVar nm sch) = liftM (TEVar nm) (zonkScheme sch)
         f (TECon mu nm rho a xs) = liftM2 (\ r x -> TECon mu nm r a x) (zonkRho rho) (mapM zonkExp xs)
         f (TEApp x y) = liftM2 TEApp (zonkExp x) (zonkExp y)
         f (TEAbs e1 ms) = liftM2 TEAbs (zonkElim2 e1)(mapM g ms)
            where g (p,e) = do { e2 <- zonkExp e; p2 <- zonkPat p; return(p2,e2)}
         f (TETuple es) = liftM TETuple (mapM zonkExp es)
         f (TELet d x) = liftM2 TELet (mapMDecl zonkExp zonkPat d) (zonkExp x)
         f (TEIn k x) = liftM2 TEIn (zonkKind k)(zonkExp x)
         f (TEMend tag elim scr ms) = liftM3 (TEMend tag) (zonkElim elim) (zonkExp scr) (mapM g ms)
            where g (tele,ps,e) = do { e2 <- zonkExp e
                                     ; ps2 <- mapM zonkPat ps
                                     ; tele2 <- (mapM zonkClass tele)
                                     ; return(tele2,ps2,e2)}
         f (AppTyp e t) = liftM2 AppTyp (zonkExp e) (mapM zonk t)
         f (AbsTyp ts e) = liftM2 AbsTyp (mapM zonkClass ts) (zonkExp e)
         f (TECast p e) = liftM2 TECast (zonkTEqual p) (zonkExp e)
         f (ContextHole e1 e2) = liftM2 ContextHole (zonkExp e1) (zonkExp e2)
         f (Emv(uniq,ptr,t)) = do { t2 <- zonk t; pruneE(Emv(uniq,ptr,t2))}
         f (CSP x) = return(CSP x)

zonkElim::  Elim (Telescope, [(Typ, Kind)]) -> FIO (Elim (Telescope, [(Typ, Kind)]))
zonkElim ElimConst = return ElimConst
zonkElim (ElimFun (tele,pairs) t) = 
   liftM2 (ElimFun) (liftM2 (,) (zonkTele tele) (mapM f pairs)) (zonk t)
  where f (t,k) = liftM2 (,) (zonk t) (zonkKind k)

zonkElim2::  Elim [(Name, Class () Kind Typ)] -> FIO (Elim [(Name, Class () Kind Typ)])
zonkElim2 ElimConst = return ElimConst
zonkElim2 (ElimFun ns t) = liftM2 (ElimFun) (mapM f ns) (zonk t)
     where f (n,Type k) = do { k2 <- zonkKind k; return(n,Type k2)}
           f (n,Exp k) = do { k2 <- zonk k; return(n,Exp k2)}
           f (n,Kind ()) = return(n,Kind ()) 



zonk :: Typ -> FIO Typ
zonk t = do { x <- prune t; f x}
  where f (TyVar s k) =  liftM (TyVar s) (zonkKind k)
        f (TyApp g x) = liftM2 TyApp (zonk g) (zonk x)      
        f (TyTuple k xs) = liftM2 TyTuple (zonkKind k) (mapM zonk xs)
        f (TyProof x y) = liftM2 TyProof (zonk x) (zonk y)
        f (TyArr x y) = liftM2 TyArr (zonk x) (zonk y)
        f (TySyn nm arity xs body) =
            liftM2 (TySyn nm arity) (mapM zonk xs) (zonk body)
        f (TyMu k) = liftM TyMu (zonkKind k)
        f (TyLift (Checked e)) = liftM (TyLift . Checked) (zonkExp e)
        f (TyLift (Parsed e)) = return(TyLift (Parsed e)) -- liftM (TyLift . Parsed) (zonkE e)                      
        f (TyCon syn c k) = do { k1 <- zonkPolyK k; return(TyCon syn c k) }
        f (TcTv (uniq,ptr,k)) =  do { k1 <- zonkKind k; return(TcTv(uniq,ptr,k1)) }
        f (TyAll vs r) =
            do { us <- mapM zonkClass vs
               ; b <- zonk r
               ; return(TyAll us b)}
     
zonkRho (Tau t) = do { a <- zonk t; return(Tau a)}
zonkRho (Rarr x y) = do { a <- zonkScheme x; b <- zonkRho y; return(Rarr a b)}

zonkClass:: (x,Class () Kind Typ) -> FIO (x,Class () Kind Typ)
zonkClass (x,Kind ()) = return (x,Kind ())
zonkClass (x,Type k) = do { k2 <- zonkKind k; return(x,Type k2)}
zonkClass (x,Exp t) = do { t2 <- zonk t; return(x,Exp t2)}

zonkTele :: Telescope -> FIO Telescope
zonkTele x = mapM zonkClass x
      
zonkScheme :: Scheme -> FIO Scheme
zonkScheme (Sch vs r) =
  do { -- let f (v,k) = do { a <- zonkKind k; return(v,a) };
       us <- mapM zonkClass vs
     ; b <- zonkRho r
     ; return(Sch us b)}
     
zonkPolyK :: PolyKind -> FIO PolyKind
zonkPolyK (PolyK vs r) =
  do { us <- mapM zonkClass vs
     ; b <- zonkKind r
     ; return(PolyK us b)}

------------------------------------------
-- Turn a scheme into a Rho type, with fresh mutable
-- variables for the universally quantified ones.

instantiate:: Scheme -> FIO (Rho,[Typ])
instantiate (Sch xs r) = do { (env@(ptrs,names,tycons)) <- freshenTele noPos xs ([],[],[])
                            ; rho <- rhoSubb noPos env r
                            ; return(rho,map unType (foldr typeAcc [] names))}
  where unType (nm,Type x) = x

rigidize:: Scheme -> FIO([Name],[Typ],Rho)
rigidize (Sch xs r) = do { (env@(ptrs,names,tycons)) <- rigidTele noPos xs ([],[],[])
                         ; ans <- rhoSubb noPos env r
                         ; return(map fst names,map ff names, ans)}
  where freshen xs = mapM g xs
        g (name,kind) = do { n <- fio(nextInteger); return(name,Type (TyVar (Nm("_"++show n,noPos)) kind)) }
        ff (nm,Type t) = t
        ff (nm,Exp e) = TyLift (Checked e)



        
existInstance:: Scheme -> FIO([Name],Rho)
existInstance (Sch xs rho) =  
  do { let split (Tau x) ts = rng x ts
           split (Rarr s r) ts = split r (s:ts)
           rng (TyArr x y) ts = rng y (Sch [] (Tau x):ts)
           -- rng (TyApp (TyApp (TyCon _ (Nm("(->)",_)) _) x) y) ts = rng y (Sch [] (Tau x):ts)
           rng x ts = return (ts,x)
     ; (doms,range) <- split rho []
     ; (rptrs,rangeNames) <- getVars range
     ; (dptrs,domNames) <- foldM (accumBy getVarsScheme) ([],[]) doms
     ; let existNames = domNames \\ rangeNames
     ; let exists nm = if (elem (Type nm) existNames) then Exist else Univ
     ; (subst@(ptrs,names,tycons)) <- newTele exists noPos xs ([],[],[])
     ; rho2 <- rhoSubb noPos subst rho
     ; let acc (nm,_) ans = case exists nm of {Exist -> nm : ans; Univ -> ans}
     ; return(foldr acc [] names,rho2)
     }

freshExistTyp :: (t, Kind) -> FIO (t,Class k Typ e)
freshExistTyp (name,kind) = 
   do { n <- fio(nextInteger)
      ; return(name,Type(TyVar (Nm("_"++show n,noPos)) kind)) }
      
existTyp:: Name -> Class () Kind Typ -> FIO (Class Kind Typ TExpr)
existTyp nm x = new Exist noPos nm ([],[],[]) x

-------------------------------------------
-- Create a scheme

-- PM is a "Pointer Map"  Mapping mutable vars to the things they abstract
type PM t = (Pointer t,t)

generalize:: Pointers -> Typ -> FIO (Scheme,[Class (PM Kind) (PM Typ) (PM TExpr)])
generalize us t = generalizeRho us (Tau t)

classToName:: Class a a a -> a
classToName (Kind nm) = nm
classToName (Type nm) = nm
classToName (Exp  nm) = nm
     
generalizeRho:: Pointers -> Rho -> FIO(Scheme,[Class (PM Kind) (PM Typ) (PM TExpr)])
generalizeRho us t =  
  do { (ptrs,badvars) <- getVarsRho t
     ; (subst@(ps,ns,ts),tele) <- ptrSubst (map classToName badvars)  ptrs nameSupply ([],[],[])
     ; body <- rhoSubb noPos subst t
     ; body2 <- alphaRho body
     ; return(Sch tele body2,ps)
     }

alphaRho (Rarr s r) = do { s' <- alpha s; r' <- alphaRho r; return(Rarr s' r')}
alphaRho (Tau t) = return(Tau t)  

alpha sch = schemeSubb noPos ([],[],[]) sch


addPointer x (ptrs,names,tycons) = (x:ptrs,names,tycons)

ptrSubst:: [Name] ->    -- Names occuring in the term, these are bad so shouldn't be used.
           Pointers ->  -- Pointers that should be generalized.
           [Name] ->    -- An infinite name supply of names to choose.
           SubEnv ->
       FIO (SubEnv,Telescope)  --  (mapping ptrs to names, telescope of classified names)
           
ptrSubst bad [] names env = return (env,[])
ptrSubst bad (ps@((Kind(uniq,ptr)):more)) (n:names) env =
  if elem n bad -- elem (Kind n) bad || elem (Type n) bad || elem (Exp n) bad
     then ptrSubst bad ps names env
     else do { (env2,tele) <- ptrSubst bad more names (addPointer (Kind(ptr,Kname n)) env)
             ; return(env2, (n,Kind ()):tele) }
              
ptrSubst bad (ps@((Type(uniq,ptr,kind)):more)) (n:names) env =
  if elem n bad -- elem (Kind n) bad || elem (Type n) bad || elem (Exp n) bad
     then ptrSubst bad ps names env
     else  do { kind1 <- kindSubb noPos env kind
              ; (env2,tele) <- ptrSubst bad more names (addPointer (Type(ptr,TyVar n kind1)) env)
              ; return(env2,(n,Type kind1):tele)}

ptrSubst bad (ps@((Exp(uniq,ptr,typ)):more)) (n:names) env =
  if elem n bad -- elem (Kind n) bad || elem (Type n) bad || elem (Exp n) bad
     then ptrSubst bad ps names env
     else do { typ1 <- tySubb noPos env typ
             ; let term = TEVar n (Sch [] (Tau typ1))
             ; (env2,tele) <- ptrSubst bad more names (addPointer (Exp(ptr,term)) env)            
             ; return (env2, (n,Exp typ):tele ) 
             }
                 

matchErr loc messages t1 t2 = fail ("\n\n*** Error, near "++show loc++"\n"++(unlines messages)) -- ++"\n   "++show t1++"\n   "++show t2)



-------------------------------------------------
-- operations on Kinds

freshKind = 
  do { n <- fio(nextInteger)
     ; p <- fio(newIORef Nothing)
     ; return(Kvar(n,p)) }
     
get_kvs:: Kind -> FIO [(Uniq,Pointer Kind)]
get_kvs k = 
  do { (ptrs,names) <- getVarsKind k
     ; let acc (Kind(u,ptr)) ans = (u,ptr):ans
           acc _ ans = ans
     ; return(foldr acc [] ptrs)}

pruneK :: Kind -> FIO Kind
pruneK (k @ (Kvar(uniq,ref))) =
  do { maybet <- fio(readIORef ref)
     ; case maybet of
         Nothing -> return k
         Just k1 -> do{k2 <- pruneK k1; fio(writeIORef ref (Just k2)); return k2}}
pruneK t = return t

unifyK :: SourcePos -> [String] -> Kind -> Kind -> FIO ()
unifyK loc message x y = do { x1 <- pruneK x; y1 <- pruneK y; f x1 y1 }
  where f (t1@(Kvar n)) (t2@(Kvar n1)) | n==n1 = return ()
        f (Karr x y) (Karr a b) = do { unifyK loc message x a; unifyK loc message y b }
        f Star Star = return ()
        f (LiftK s) (LiftK  t) = unify loc message s t
        f (Kname x) (Kname y) | x==y = return()
        f (Kvar x) t = unifyVarK loc message x t
        f t (Kvar x) = unifyVarK loc message x t 
        f s t = do { s2 <- zonkKind s; t2 <- zonkKind t
                   ; matchErr loc (("\nDifferent kinds "++showK s2++" =/= "++showK t2): message)  s2 t2 
                   }

unifyVarK loc message (uniq,r1) t =
  do { vs <- get_kvs t
     ; if (any (==(uniq,r1)) vs) 
          then do { t2 <- zonkKind t
                  ; (matchErr loc (("\nKind occurs check "++show uniq++" in "++show (map fst vs)): message)  (Kvar(uniq,r1)) t2)}
          else return ()
     ; fio(writeIORef r1 (Just t))
     ; return ()
     }

zonkKind x = do { x1 <- pruneK x; f x1}
  where f (Kvar n) = return (Kvar n)
        f (Karr x y) = do { a <- zonkKind x; b <- zonkKind y; return(Karr a b) }
        f Star = return Star
        f (LiftK b) = do { c <- zonk b; return(LiftK c)}
        f (Kname n) = return(Kname n)


---------------------------------------------

-- Collecting Variables, both Pointers and Names

type Pointers = 
       [Class (Uniq, Pointer Kind)
              (Uniq, Pointer Typ, Kind)
              (Uniq, Pointer TExpr, Typ)]
type Names = [Class Name Name Name]                       
type Vars = (Pointers, Names)

remove _ [] ns = []
remove x (m : more) ns =
  case (x,m) of
   (Kind _,Kind s) ->
     if elem s ns then remove x more ns else m : (remove x more ns)
   (Type _,Type s) ->
     if elem s ns then remove x more ns else m : (remove x more ns)
   (Exp _,Exp s) ->
     if elem s ns then remove x more ns else m : (remove x more ns)
   (_,_) -> m : (remove x more ns)


unionW:: Vars -> Vars -> FIO Vars
unionW (xs,ys) (ms,ns) =  liftM2 (,) (unionByM (f h) xs ms) (unionByM (f g) ys ns)
  where h (Kind(uniq,ptr)) = (uniq,"Kind",noPos,"k"++show uniq)
        h (Type(uniq,ptr,kind)) = (uniq,"Type",loc kind,"t"++show uniq)
        h (Exp(uniq,ptr,typ)) = (uniq,"Exp",loc typ,"e"++show uniq)
        g (Kind x) = (x,"Kind",loc x,show x)
        g (Type x) = (x,"Type",loc x,show x)
        g (Exp x) = (x,"Exp",loc x,show x)
        f strip x y = 
           case (strip x,strip y) of
            ((u1,tag1,pos1,nm1),(u2,tag2,pos2,nm2)) 
              | u1==u2 && tag1==tag2 -> return True
              | u1==u2 -> fail("\n*** Error ***\nThe variable: "++nm1++" is used inconsistently as a\n   "++
                               tag1++", near "++show pos1++"\nand as a\n   "++
                               tag2++", near "++show pos2++"\nPerhaps you forgot some braces { }?")
              | otherwise -> return False
{-  
  where f (Kind (u1,p1))    (Kind (u2,p2))    = u1==u2
        f (Type (u1,p1,k1)) (Type (u2,p2,k2)) = u1==u2
        f (Exp  (u1,p1,t1)) (Exp  (u2,p2,t2)) = u1==u2
        f _ _ = False
        g (Kind x) (Kind y) = x==y
        g (Type x) (Type y) = x==y
        g (Exp  x) (Exp  y) = x==y
        g _ _ = False        
-}

accumBy f trip1 x = do { trip2 <- f x; (unionW trip1 trip2)}   


kindAcc (nm,Kind e) ans = (nm,Kind e):ans
kindAcc _ ans = ans

typeAcc (x,Type t) ans = (x,Type t) : ans
typeAcc (x,Exp e) ans = (x,Type(TyLift (Checked e))) : ans
typeAcc _ ans = ans

typeAccDrop (Type t) ans = t:ans
typeAccDrop _ ans = ans

expAcc (x,Exp e) ans = (x,Exp e) :ans
expAcc _ ans = ans


------------------------------------------------------------- 

getVarsElim:: Elim Telescope -> FIO Vars
getVarsElim ElimConst = return ([],[])
getVarsElim (ElimFun ns t) = 
  do { x1 <- getVars t
     ; getVarsTele ns x1}
     
getVarsElim2:: Elim [Typ] -> FIO Vars
getVarsElim2 ElimConst = return ([],[])
getVarsElim2 (ElimFun ns t) = 
  do { trip <- getVars t
     ; foldM (accumBy getVars) trip ns }  
  
getVarsE:: Expr -> FIO Vars
getVarsE t = f t
  where f (ELit pos lit) = return([],[])
        f (ECon v) = return([],[])
        f (EVar v) = return([],[Exp v])
        f (EFree v) = return([],[])   -- v will elaborate to a CSP constant
        f (EApp x y) =
          do { trip1 <- getVarsE x 
             ; trip2 <- getVarsE y
             ; (unionW trip1 trip2)}
        f (EAbs e1 cls) = error ("No getVarsE for (EAbs _ _) yet")   
{-
        f (TEAbs e1 cls) = do { v1 <- getVarsElim e1 
                              ; foldM (accumBy free) v1 cls }
                           
            where free (pat,exp) = 
                   do { pair1 <- getVarsElim e1
                      ; pair2 <- getVarsExpr exp 
                      ; (ptrs,vars) <- unionW pair1 pair2
                      ; return (ptrs,remove (Exp 0) vars (patBinds pat [])) }
-}        
        f (ETuple xs) = foldM (accumBy getVarsE) ([],[]) xs
        f (EIn k x) = do { a <- getVarsKind k; b <- getVarsE x; unionW a b}
        f (ELet d e) = error ("No getVarsE for (ELet _ _) yet")    
        f (EMend _ _ _ _ ) = error ("No getVarsE for (EMend _ _ _ _) yet")    

-- is a variable a type constructor?
conP (Nm(c:cs,pos)) = isUpper c
conP _ = False     

getVarsExpr:: TExpr -> FIO Vars
getVarsExpr t = do { x <- pruneE t; f x }
  where f (TELit pos lit) = return([],[])
        f (TEVar v sch) = 
          do { pair <- getVarsScheme sch
             ;  if conP v
                  then return pair
                  else  (unionW pair ([],[Exp v]) )}
        f (TECon mu c rho arity xs) = 
          do { v1 <- foldM (accumBy getVarsExpr) ([],[]) xs
             ; v2 <- getVarsRho rho
             ; unionW v1 v2}
        f (TEApp x y) =
          do { trip1 <- getVarsExpr x 
             ; trip2 <- getVarsExpr y
             ; (unionW trip1 trip2)}
        f (TEAbs e1 cls) = do { v1 <- getVarsElim e1 
                              ; foldM (accumBy free) v1 cls }
                           
            where free (pat,exp) = 
                   do { pair1 <- getVarsElim e1
                      ; pair2 <- getVarsExpr exp 
                      ; (ptrs,vars) <- unionW pair1 pair2
                      ; return (ptrs,remove (Exp 0) vars (patBinds pat [])) }

        f (TETuple xs) = foldM (accumBy getVarsExpr) ([],[]) xs
        f (TEIn k x) = do { a <- getVarsKind k; b <- getVarsExpr x; unionW a b}
        f (Emv p) = return([Exp p],[]) 
        f (AppTyp x ts) =
	  do { trip1 <- getVarsExpr x 
	     ; foldM (accumBy getVars) trip1 ts} 	     
        f (AbsTyp xs y) =
	  do { trip1 <- getVarsExpr y
	     ; getVarsTele xs trip1 }
	f (TECast (TGen xs x) y) = 
	  do { trip1 <- getVarsTEqual x
	     ; trip2 <- getVarsExpr y
	     ; trip3 <- unionW trip1 trip2
	     ; getVarsTele xs trip3 }
        f (TECast p e) = 
          do { trip1 <- getVarsTEqual p
	     ; trip2 <- getVarsExpr e
             ; (unionW trip1 trip2)}	     
        f (TEMend tag elim arg ms) = error ("No getVarsExp for (EMend _ _ _) yet")	 
        f (TELet _ _) = error ("No getVarsExp for (ELet _ _) yet")
        f (CSP _) = return([],[])
        f (ContextHole x y ) = 
          do { trip1 <- getVarsExpr x 
             ; trip2 <- getVarsExpr y
             ; (unionW trip1 trip2)}        

getVarsKind:: Kind -> FIO Vars
getVarsKind k =  do { x <- pruneK k; f x }
  where f Star = return ([],[])
        f (Karr x y) =
          do { trip1 <- getVarsKind x 
             ; trip2 <- getVarsKind y
             ; (unionW trip1 trip2)}
        f (LiftK t) = getVars t
        f (Kvar p) = return ([Kind p],[])
        f (Kname n) = return ([],[Kind n])

getVarsPolyK (PolyK xs y) =
   do { trip1 <- getVarsKind y; getVarsTele xs trip1 }        

getVars:: Typ -> FIO Vars
getVars t = do { x <- prune t; f x }
  where f (TyVar n k) = 
          do { pair <- getVarsKind k
             ; (unionW pair ([],[Type n]))}
        f (TyApp x y) =
          do { trip1 <- getVars x 
             ; trip2 <- getVars y
             ; (unionW trip1 trip2)}    
        f (TyTuple k xs) = 
           do { trip <- getVarsKind k
              ; foldM (accumBy getVars) trip xs }             
        f (TyCon _ s k) = getVarsPolyK k
        f (TyProof x y) = 
          do { trip1 <- getVars x 
             ; trip2 <- getVars y
             ; (unionW trip1 trip2)}   
        f (TyArr x y) = 
          do { trip1 <- getVars x 
             ; trip2 <- getVars y
             ; (unionW trip1 trip2)}  
        f (TySyn nm arity xs body) = 
          do { trip3 <- getVars body
             ; foldM (accumBy getVars) trip3 xs }
        f (TyMu k) = getVarsKind k
        f (TyLift (Checked e)) = getVarsExpr e       
        f (TyLift (Parsed e)) = getVarsE e
--         f (TyLift (Pattern p)) = return([],map Exp (patBinds p []))
        f (TcTv (t@(uniq,ptr,k))) = 
          do { pair <- getVarsKind k             
             ; (unionW pair ([Type t],[])) }
        f (TyAll bound r) = do { vs <- getVars r; getVarsTele bound vs }             
                       
getVarsRho (Tau t) = getVars t
getVarsRho (Rarr s r) = 
  do { trip1 <- getVarsScheme s
     ; trip2 <- getVarsRho r
     ; (unionW trip1 trip2)}

getVarsScheme (Sch bound r) = 
    do { vs <- getVarsRho r; getVarsTele bound vs }
 
getVarsTele:: Telescope -> Vars -> FIO Vars      
getVarsTele [] ans = return ans
getVarsTele (pair:more) ans = do { env1 <- getVarsTele more ans; getVarsClass pair env1 } 
  where rem tag (ptrs,names) bound = (ptrs,remove tag names bound)
        getVarsClass (nm,Kind ()) env = return(rem (Kind 0) env [nm])
        getVarsClass (nm,Type k) env = 
          do { env2 <- getVarsKind k
             ; (unionW env2 (rem (Type 0) env [nm])) }
        getVarsClass (nm,Exp t) env = 
          do { env2 <- getVars t
             ; (unionW env2 (rem (Type 0) env [nm])) }   
     

-------------------------------------------------------------

type SubEnv = 
      ([Class (Pointer Kind,Kind)     -- Pointers to coresponding objects
              (Pointer Typ,Typ)
              (Pointer TExpr,TExpr)]            
      ,[(Name,Class Kind Typ TExpr)]  -- Names to Objects
      ,[(Name,Typ)]                   -- TyCon names to Typ
      )

findE _ [] ans = ans
findE (Kind x) (Kind(y,e):more) ans = if x==y then Kind e else findE (Kind x) more ans
findE (Type x) (Type(y,e):more) ans = if x==y then Type e else findE (Type x) more ans
findE (Exp x)  (Exp(y,e):more)  ans = if x==y then Exp e else findE (Exp x)  more ans
findE x (m:more) ans = findE x more ans

findF _ [] ans = ans
findF (Kind x) ((y,Kind e):more) ans = if x==y then Kind e else findF (Kind x) more ans
findF (Type x) ((y,Type e):more) ans = if x==y then Type e else findF (Type x) more ans
findF (Exp x)  ((y,Exp e):more)  ans = if x==y then Exp e else findF (Exp x)  more ans
findF x (m:more) ans = findF x more ans


hideE p (ptrs,names,tycons) = (ptrs,filter (patBinds p []) names,tycons)
  where filter ns [] = []
        filter ns ((y,Exp t): more) | elem y ns = filter ns more
        filter ns (m:more) = m : filter ns more
        
hideT ns (ptrs,names,tycons) = (ptrs,filter ns names,tycons)
  where filter ns [] = []
        filter ns ((y,Type t): more) | elem y ns = filter ns more
        filter ns (m:more) = m : filter ns more        
 
------------------------------------------------------------
-- Operations on telescopes

rigidName (Nm(n,pos)) =
  do { u <- unique ""; return(Nm("_"++n++u,pos))}
 
freshName (Nm(n,pos)) =
  do { u <- unique ""; return(Nm(n++u,pos))}

freshName2 (Nm(n,pos)) = 
  do { m <- fio(nextInteger); return(Nm(n++show m,pos))}
  
data InstanTag 
    = Univ    -- completely replace each name with a fresh mutable variable
    | Exist   -- completely replace each name with a rigid existential variable

new:: InstanTag -> SourcePos -> Name -> SubEnv 
      -> Class () Kind Typ 
      -> FIO (Class Kind Typ TExpr)
new Univ pos nm env (Kind ()) = do { k <- freshKind; return(Kind k)}
new Univ pos nm env (Type k) = do { k2 <- kindSubb pos env k; t <- freshType k2; return(Type t)}
new Univ pos nm env (Exp t) = do { t2 <- tySubb pos env t; e <- freshExp t2; return(Exp e)}
new Exist pos nm env x =
  do { nm2 <- rigidName nm
     ; case x of
         Kind () -> return(Kind(Kname nm2))
         Type k -> do { k2 <- kindSubb pos env k; return (Type(TyVar nm2 k2)) }
         Exp t ->  do { t2 <- tySubb pos env t
                      ; liftM Exp (rigidVar nm2 t2) } }
                      -- return(Exp(TEVar nm2 (Sch [] (Tau t2)))) }} 

rigidVar nm ty = do { i <- next; return(CSP(nm,i,VCode(TEVar nm (Sch [] (Tau ty)))))}

newTele :: (Name -> InstanTag) -> SourcePos -> Telescope -> SubEnv -> FIO(SubEnv)
newTele tagf pos [] env = return (env)
newTele tagf pos ((nm,x):xs) (env@(ptrs,names,tycons)) =
  do { y <- new (tagf nm) pos nm env x
     ; (env) <- newTele tagf pos xs (ptrs,(nm,y):names,tycons)
     ; return(env)}
                    
freshenTele :: SourcePos -> Telescope -> SubEnv -> FIO(SubEnv)
freshenTele pos tele env = newTele (const Univ) pos tele env

rigidTele :: SourcePos -> Telescope -> SubEnv -> FIO(SubEnv)
rigidTele pos tele env = newTele (const Exist) pos tele env

rigidElim:: SourcePos -> Elim Telescope -> FIO (SubEnv, [Typ], Typ)
rigidElim pos (ElimConst) = do { t <- freshType Star; return(([],[],[]),[],t)}
rigidElim pos (ElimFun xs body) = 
   do{ subst@(_,names,_) <- rigidTele pos xs ([],[],[]) 
     ; ts <- teleToTyList (reverse names)   -- order matters here
     ; body2 <- tySubb pos subst body
     ; writeln("RigidElim "++show body++" -> "++show body2++" via "++show names)
     ; return(subst,ts,body2) }

freshElim:: SourcePos -> Elim Telescope -> FIO (SubEnv, [Typ], Typ)
freshElim pos (ElimConst) = do { t <- freshType Star; return(([],[],[]),[],t)}
freshElim pos (ElimFun xs body) = 
   do{ subst@(_,names,_) <- freshenTele pos xs ([],[],[]) 
     ; ts <- teleToTyList (reverse names) -- order matters here, but not in the Subst
     ; body2 <- tySubb pos subst body
     ; return(subst,ts,body2) }
     
teleToTyList:: [(Name, Class t Typ TExpr)] -> FIO [Typ]
teleToTyList xs = mapM f xs
  where f(nm,Kind k) = fail ("Large eliminations can't abstract over kinds: "++show nm)
        f(nm,Type t)  = return t
        f(nm,Exp e)   = return(TyLift (Checked e))
     

-------------------------------------------------------------------------

getNamesSubEnv :: SubEnv -> FIO [Name]
getNamesSubEnv (ptrs,names,tycons) = 
           do { ns1 <- foldM getptr [] ptrs
              ; ns2 <- foldM getname ns1 names
              ; foldM getcon ns2 tycons }
  where getptr ans  (Kind(ptr,k)) = do { (_,cl) <- getVarsKind k; return(map classToName cl ++ ans)}
        getptr ans  (Type(ptr,t)) = do { (_,cl) <- getVars t; return(map classToName cl ++ ans)}
        getptr ans  (Exp(ptr,e))  = do { (_,cl) <- getVarsExpr e; return(map classToName cl ++ ans)}
        getname ans (nm,Kind k)   = do { (_,cl) <- getVarsKind k; return(map classToName cl ++ ans)}
        getname ans (nm,Type t)   = do { (_,cl) <- getVars t; return(map classToName cl ++ ans)}
        getname ans (nm,Exp e)    = do { (_,cl) <- getVarsExpr e; return(map classToName cl ++ ans)}
        getcon  ans (nm,t)        = do { (_,cl) <- getVars t; return(map classToName cl ++ ans)}

freshFor:: Name -> SubEnv -> [Name] -> FIO Name
freshFor name env supply = do { bad <- getNamesSubEnv env; worker name bad supply }
  where worker name bad (n:ns) = if elem name bad then worker n bad ns else return name


-- widen (Kind (nm,nm2)) (ptrs,names,tycons) = (ptrs,(nm,Kind(Kname nm2)):names,tycons)


freshForTyp:: (Typ, Class () Kind Typ) -> SubEnv -> [Name] -> FIO Typ
freshForTyp (typ,tag) env supply = 
    do { (_,names) <- getVars typ
       ; return (error "Fresh for type, not yet")
       }

alphaTele :: SourcePos -> (Telescope,SubEnv) -> FIO (Telescope,SubEnv)
alphaTele pos ([],env) = return ([],env)
alphaTele pos ((nm,Kind ()):xs,env) =   
  do { nm2 <- freshFor nm env nameSupply -- freshName nm
     ; let widen (ptrs,names,tycons) = (ptrs,(nm,Kind(Kname nm2)):names,tycons)
     ; (ys,env2) <- alphaTele pos (xs,widen env)
     ; return((nm2,Kind ()):ys,env2)}
alphaTele pos ((nm,Type k):xs,env) =
  do { nm2 <- freshFor nm env nameSupply -- freshName nm
     ; k2 <- kindSubb pos env k
     ; let widen (ptrs,names,tycons) = (ptrs,(nm,Type(TyVar nm2 k2)):names,tycons)
     ; (ys,env2) <- alphaTele pos (xs,widen env)
     ; return((nm2,Type k2):ys,env2)}
alphaTele pos ((nm,Exp t):xs,env) =
  do { nm2 <- freshFor nm env nameSupply -- freshName nm
     ; t2 <- tySubb pos env t
     ; let widen (ptrs,names,tycons) = (ptrs,(nm,Exp(TEVar nm2 (Sch [] (Tau t)))):names,tycons)
     ; (ys,env2) <- alphaTele pos (xs,widen env)
     ; return((nm2,Exp t2):ys,env2)}     
          
instanK:: SourcePos -> PolyKind -> FIO Kind
instanK pos (PolyK xs k) =  
  do { (subst) <- freshenTele pos xs ([],[],[])
     ; kindSubb pos subst k }

---------------------------------------------------------------------------
-- In an elimination we are allowed to write a list of types
-- { t (List t {succ n}) (Fin n) . body }
-- we need to compute which variables are bound
-- Here, both "t" and "n" are bound in "body"


notIn x env = case lookup x env of { Nothing -> False; Just _ -> True }     

threadM f ([],env) = return([],env)
threadM f (x:xs,env) = 
   do { (x2,env2) <- f (x,env)
      ; (xs2,env3) <- threadM f (xs,env2)
      ; return(x2:xs2,env3) }
       
       

tbinds::(Typ,[(Name, Class Kind Typ TExpr)]) -> FIO(Typ,[(Name, Class Kind Typ TExpr)])
tbinds (t,env) = do { t2 <- prune t; help t2 } where
  help (TyVar nm k) | notIn nm env = 
    do { nm2 <- freshFor nm ([],env,[]) nameSupply 
       ; return(TyVar nm2 k,(nm,Type(TyVar nm2 k)): env) }
  help (t@(TyVar _ _)) = return(t,env)     
  help (TyApp f x) = 
     do { (f2,env2) <- tbinds (f,env); (x2,env3) <- tbinds (x,env2); return(TyApp f2 x2,env3) }
  help (TyTuple k ts) = 
     do { (ts2,env2) <- threadM tbinds (ts,env); return(TyTuple k ts2,env2)}
  help (TyCon m n p) = return(TyCon m n p,env)
  help (TyProof f x) = 
     do { (f2,env2) <- tbinds (f,env); (x2,env3) <- tbinds (x,env2); return(TyProof f2 x2,env3) }
  help (TyArr f x) = 
     do { (f2,env2) <- tbinds (f,env); (x2,env3) <- tbinds (x,env2); return(TyArr f2 x2,env3) }
  help (TySyn nm arity ts b) =
     do { (ts2,env2) <- threadM tbinds (ts,env)
        ; (b2,env3) <- tbinds (b,env2)
        ; return(TySyn nm arity ts2 b2,env3) }
  help (TyMu k) = do { (k2,env2) <- kbinds (k,env); return(TyMu k2,env2)}
  help (TcTv x) = return(TcTv x,env)
  help (TyLift (Checked e)) = do { (e2,env2) <- ebinds (e,env); return(TyLift (Checked e2),env2)}
  help (TyLift e) = fail("Unchecked term in tbinds: "++show e)
  help (TyAll vs t) = error ("TyAll in ebinds")
  
ebinds:: (TExpr,[(Name, Class Kind Typ TExpr)]) -> FIO(TExpr,[(Name, Class Kind Typ TExpr)]) 
ebinds (e,env) = do { e2 <- pruneE e; help e2 }  where
  help (TEVar nm s) | notIn nm env = 
     do { nm2 <- freshFor nm ([],env,[]) nameSupply 
        ; return(TEVar nm2 s,(nm,Exp(TEVar nm2 s)):env) }
  help (e@(TEVar _ _)) = return(e,env)
  help (TELit pos x) = return(TELit pos x,env)
  help (TEApp f x) = 
     do { (f2,env2) <- ebinds (f,env); (x2,env3) <- ebinds (x,env2); return(TEApp f2 x2,env3) }
  help (e@(TEAbs _ _)) = fail("Not yet (TEAbs _ _) in ebinds: "++show e)
  help (TETuple ts) = 
     do { (ts2,env2) <- threadM ebinds (ts,env); return(TETuple ts2,env2)}  
  help (e@(TELet _ _)) = fail("Not yet (TELet _ _) in ebinds: "++show e)
  help (TEIn k x) = 
    do { (x2,env2) <- ebinds (x,env); (k2,env3) <- kbinds (k,env2); return(TEIn k2 x2,env3) }
  help (e@(TEMend _ _ _ _)) = fail("Not yet (TEMend _ _ _ _) in ebinds: "++show e)
  help (AppTyp x ts) = do { (x2,env2) <- ebinds (x,env); return(AppTyp x2 ts,env2) }
  help (AbsTyp ts x) = do { (x2,env2) <- ebinds (x,env); return(AbsTyp ts x2,env2) }  
  help (TECast p x) = do { (x2,env2) <- ebinds (x,env); return(TECast p x2,env2) }
  help (ContextHole x y) = return(ContextHole x y,env)
  help (Emv x) = return(Emv x,env)
  help (CSP x) = return(CSP x,env)

kbinds :: (Kind, [(Name, Class Kind Typ TExpr)]) -> FIO (Kind, [(Name, Class Kind Typ TExpr)])  
kbinds (k,env) = do { k2 <- pruneK k; help k2 } where
  help Star = return(Star,env)
  help (Kname nm) | notIn nm env = 
     do { nm2 <- freshFor nm ([],env,[]) nameSupply 
        ; return(Kname nm2,(nm,Kind(Kname nm2)):env)}
  help (e@(Kname _ )) = return(e,env)
  help (LiftK t) = do { (t2,env2) <- tbinds (t,env); return(LiftK t2,env2)}
  help (Karr f x) = 
     do { (f2,env2) <- kbinds (f,env); (x2,env3) <- kbinds (x,env2); return(Karr f2 x2,env3) } 
  help (Kvar x) = return(Kvar x,env)     
 
freshElimPairs:: SourcePos -> ([(Typ,Kind)],SubEnv) -> FIO([(Typ,Kind)],SubEnv) 
freshElimPairs pos ([],env) = return ([],env)
freshElimPairs pos ((t,k):ps,env@(ptrs,names,tycons)) = 
  do { k2 <- kindSubb pos env k
     ; (t2,names2) <- tbinds (t,names)
     ; t3 <- tySubb pos env t2
     ; (ps2,env2) <- freshElimPairs pos (ps,(ptrs,names2,tycons))
     ; return((t3,k2):ps,env2)}
     
------------------------------------------------------------------

decSubb:: SourcePos -> SubEnv -> Decl TExpr -> FIO (Decl TExpr)
decSubb pos env x = mapMDecl (expSubb pos env) (patSubb pos env) x
   
kindSubb:: SourcePos -> SubEnv -> Kind -> FIO Kind
kindSubb loc (env@(ptrs,names,tycons)) x = do { y <- pruneK x; f y}
  where sub x = kindSubb loc env x
        f Star = return(Star)
        f (Karr x y) = liftM2 Karr (sub x) (sub y)
        f (LiftK t) = liftM LiftK (tySubb loc env t)
        f (k@(Kvar (uniq,ptr))) = returnK (findE (Kind ptr) ptrs (Kind k))
        f (Kname n) = returnK(findF (Kind n) names (Kind(Kname n)))

polyKindSubb:: SourcePos -> SubEnv -> PolyKind -> FIO PolyKind 
polyKindSubb pos env (PolyK ts k) =
   do { (vs2,env2) <- alphaTele pos (ts,env)
      ; k2 <- kindSubb pos env2 k
      ; return(PolyK vs2 k2)}  
                 
elimSubb:: SourcePos -> SubEnv -> Elim Telescope -> FIO (Elim Telescope)
elimSubb pos env ElimConst = return ElimConst
elimSubb pos env (ElimFun vs t) = 
    do { (vs2,env2) <- alphaTele pos (vs,env)
       ; t2 <- tySubb pos env2 t
       ; return(ElimFun vs2 t2)}
       
elimSubb2:: SourcePos -> SubEnv -> Elim (Telescope,[(Typ,Kind)]) -> FIO (Elim (Telescope,[(Typ,Kind)]))
elimSubb2 pos env ElimConst = return ElimConst
elimSubb2 pos (env@(ptrs,names,tycons)) (ElimFun (vs,ts) t) =  -- note the vs are binding occurences
  do { (vs2,env2) <- alphaTele pos (vs,env)
     ; ts2 <- mapM (\ (t,k) -> liftM2 (,) (tySubb pos env2 t) (kindSubb pos env2 k))  ts
     ; t2 <- tySubb pos env2 t
     ; return(ElimFun (vs2,ts2) t2)}
  {-
  do { (vs2,env2) <- freshElimPairs pos (vs,env)
     ; t2 <- tySubb pos env2 t
     ; return(ElimFun vs2 t2)}
 -}
 
expSubb:: SourcePos -> SubEnv -> TExpr -> FIO TExpr
expSubb pos (env@(ptrs,names,tycons))  x = do { y <- pruneE x; f y}
   where sub x = expSubb pos env x
         f (TELit loc l) = return(TELit loc l)
         f (TEVar nm sch) = 
           do { sch2 <- schemeSubb pos env sch
              ; returnE(findF (Exp nm) names (Exp (TEVar nm sch2)))}
         f (TECon mu nm rho arity xs) =
           liftM2 (\ r x -> TECon mu nm r arity x) (rhoSubb pos env rho) (mapM sub xs)
         f (TEApp x y) = liftM2 TEApp (sub x) (sub y)
         f (TEAbs e1 ms) = liftM2 TEAbs (elimSubb pos env e1) (mapM g ms)
              where g (p,e) = do { p2 <- patSubb pos env p
                                 ; e2 <- expSubb pos (hideE p env) e
                                 ; return(p2,e2)}
         f (TETuple es) = liftM TETuple (mapM sub es)
         f (TELet d x) = liftM2 TELet (decSubb pos env d) (sub x)
         f (TEIn k x) = liftM2 TEIn (kindSubb pos env k) (sub x)

         f (TEMend tag e1 scr ms) = liftM3 (TEMend tag) (elimSubb2 pos env e1) (sub scr) (mapM g ms)
            where g (tele,ps,e) = 
                     do { (vs2,env2) <- alphaTele pos (tele,env)
                        ;  ps2 <- mapM (patSubb pos env2) ps
                        ; e2 <- expSubb pos (foldr hideE env2 ps) e
                        ; return(vs2,ps2,e2)}

         f (AppTyp e t) = liftM2 AppTyp (sub e) (mapM (tySubb pos env) t)
         f (AbsTyp ts e) = 
            do { (vs2,env2) <- alphaTele pos (ts,env)
	       ; e2 <- expSubb pos env2 e
               ; return(AbsTyp vs2 e2)}  
         f (TECast (TGen ts t) e) =
           do { (vs2,env2) <- alphaTele pos (ts,env)
              ; e2 <- expSubb pos env2 e
              ; t2 <- eqSubb pos env2 t
              ; return(TECast (TGen vs2 t2) e2)}
         f (TECast p e) = liftM2 TECast (eqSubb pos env p) (expSubb pos env e)
         f (Emv(uniq,ptr,t)) = 
            do { t2 <- tySubb pos env t
               ; returnE(findE (Exp ptr) ptrs (Exp(Emv(uniq,ptr,t2))))}
         f (ContextHole e1 e2) = liftM2 ContextHole (sub e1) (sub e2)
         f (CSP x) = return(CSP x)

patSubb :: SourcePos -> SubEnv -> Pat -> FIO Pat
patSubb loc env (PVar x (Just t)) = liftM (PVar x . Just) (tySubb loc env t)
patSubb loc env (PTuple ps) = liftM PTuple (mapM (patSubb loc env) ps)
patSubb loc env (PCon c ps) = liftM (PCon c) (mapM (patSubb loc env) ps)
patSubb loc env p = return p

tySubb :: SourcePos -> SubEnv -> Typ -> FIO Typ
tySubb loc (env@(ptrs,names,tycons)) x = do { a <- prune x; f a }
  where sub x = tySubb loc env x
        f (typ@(TyVar s k)) =
          do { k2 <- kindSubb loc env k
             ; returnT(findF (Type s) names (Type (TyVar s k2)))}
        f (TyApp g x) = liftM2 TyApp (sub g) (sub x)      
        f (TyTuple k xs) = liftM2 TyTuple (kindSubb loc env k) (mapM sub xs)       
        f (typ@(TyCon syn c k)) = 
           case lookup c tycons of
             Nothing -> liftM (TyCon syn c) (polyKindSubb loc env k)
             Just t -> return t
        f (TyProof x y) = liftM2 TyProof (sub x) (sub y)
        f (TyArr x y) = liftM2 TyArr (sub x) (sub y)
        f (TySyn nm arity xs body) = liftM2 (TySyn nm arity) (mapM sub xs) (sub body)
        f (TyMu k) = liftM TyMu (kindSubb loc env k)        
        f (TyLift (Checked e)) = liftM (TyLift . Checked) (expSubb loc env e)
        f (TyLift (Parsed e)) = fail ("unchecked term in type inside tySubb: "++show e)        
        f (TcTv (uniq,ptr,k)) = 
          do { k2 <- kindSubb loc env k
             ; returnT(findE (Type ptr) ptrs (Type (TcTv (uniq,ptr,k2))))}
        f (TyAll vs t) =
          do { (vs2,env2) <- alphaTele loc (vs,env)
             ; t2 <- tySubb loc env2 t
             ; return(TyAll vs2 t2)}
    
rhoSubb loc env (Tau t) = do {a <- tySubb loc env t; return(Tau a)}
rhoSubb loc env (Rarr s r) = do { a <- schemeSubb loc env s; b <- rhoSubb loc env r; return(Rarr a b)}

schemeSubb:: SourcePos -> SubEnv -> Scheme -> FIO Scheme
schemeSubb pos (env@(ptrs,names,tycons)) (Sch vs t) =
  do { (vs2,env2) <- alphaTele pos (vs,env)
     ; t2 <- rhoSubb pos env2 t
     ; return(Sch vs2 t2)}

-----------------------------------------------------------------
-- Checking that one type is more polymorphic than another

----------------------------------------------------------------

inferLit :: Literal -> (Typ,Literal)
inferLit x@(LInteger n)= (tinteger,x)
inferLit x@(LInt n)    = (tint,x)
inferLit x@(LDouble n) = (tdouble,x)
inferLit x@(LChar c)   = (tchar,x) 
inferLit x@(LUnit)     = (tunit,x)

typeOf x = do { r <- checkExp x
              ; case r of
                 (Tau t) -> return t
                 (Rarr _ _) -> fail("Poly type in typeOf: "++show x)}

checkExp :: TExpr -> FIO Rho
checkExp (TELit loc x) = return(Tau(fst(inferLit x)))
checkExp (TEVar v sch) = do {(rho,ts) <- instantiate sch; return rho}
checkExp (TECon mu c rho arity xs) = return rho
checkExp (e@(TEApp fun arg)) =
     do { (fun_ty) <- checkExp fun
        ; (arg_ty, res_ty, p) <- unifyFunT (loc fun) ["\nWhile checking that "++show fun++" is a function"] fun_ty
        ; let message = ["\nTyping the application: ("++show e++") where\n   "++show fun++": "++show fun_ty]
        ; case arg_ty of
           Sch [] argRho -> do { x <- checkExp arg                                               
                               ; morepolyRRT (loc arg) ["arg more polymorphic than expected"] x argRho
                               ; return res_ty }                                                              
           sigma -> do { ty <- checkExp arg  
                       ; (sig,sub) <- generalizeRho [] ty  -- The [] is NOT RIGHT
                       ; sigma2 <- zonkScheme sigma >>= alpha
                       ; let m2 =("\nThe argument: "++show arg++
                                  "\nis expected to be polymorphic: "++ show sigma2):message
                       ; morepolySST (loc arg) m2 sig sigma2
                       ; return res_ty } }  
checkExp (e@(TEAbs elim cls)) =   
   fail ("Not yet in checkExp (TEAbs __): "++show e)
checkExp (TETuple xs) =
  do { let f term = checkExp term >>= unTau
           unTau (Tau t) = return t
           unTau x = error "Polymorphic tuple"
     ; xs2 <- mapM f xs   
     ; return(Tau(TyTuple Star xs2)) } 
checkExp (e@(TELet d b)) =   
   fail ("Not yet in checkExp (TELet __): "++show e)  
checkExp (TEIn k x) =   
  do { (dom,rng) <- inType k
     ; Tau x2 <- checkExp x 
     ; unify noPos ["Checking In expr"++ show (TEIn k x)] dom x2
     ; return (Tau rng)}
checkExp (e@(TECast p x)) =  fail ("Not yet in checkExp (TECast_ _): "++show e)  
checkExp (e@(ContextHole x y)) =  fail ("Illegal ContextHole in checkExp: "++show e)  
checkExp (e@(TEMend tag elim x ms)) = 
   fail ("Not yet in checkExp (TEMend _ _ _ _): "++show e)  
checkExp (e@(AppTyp t ts)) = checkExp t
   -- fail ("Not yet in checkExp (AppTyp _ _): "++show e) 
checkExp (e@(AbsTyp tele t)) = checkExp t
   -- fail ("Not yet in checkExp (AbsTyp _ _): "++show e) 
checkExp (Emv (uniq,ptr,t)) = return(Tau t) 
checkExp (CSP _) = freshRho Star
-- checkExp other = error ("Not yet in check Exp: "++show other)


-- In *           : f (Mu * f) -> Mu * f
-- In (k -> *)    : f (Mu (k->*) f n) n -> Mu (k->*) f n
-- In (k1->k2->*) : f (Mu (k1->k2->*) f i j) i j -> Mu (k1->k2->*) f i j


inType :: Kind -> FIO (Typ, Typ)
inType k = help k k []
  where help all Star ts =  
          do { f <- freshType (Karr all all)
             ; let muF = TyApp (TyMu all) f 
             ; return(applyT(f : muF : ts),applyT (muF : ts)) }
        help all (Karr k1 k2) ts = 
          do { t <- freshType k1
             ; help all k2 (ts++[t]) }
              
{-
-----------------------------------------------
-- pure substitution. Does NOT check the kind of things subbed.
-- useful after parsing when parsed things have bad kinds
-- to replace those with well-formed versions

look x xs def =
  case lookup x xs of
    Nothing -> def
    Just t -> t

subTyp :: ([(Pointer Typ,Typ)],[(Name,Typ)],[(Name,Typ)]) -> Typ -> Typ
subTyp (_,xs,_) (typ@(TyVar s k)) = look s xs typ
subTyp env (TyApp f x) = TyApp (subTyp env f) (subTyp env x)
subTyp env (TyTuple k xs) = TyTuple k (map (subTyp env) xs)
subTyp (_,_,xs) (typ@(TyCon c k)) = look c xs typ
subTyp (xs,_,_) (typ@(TcTv (uniq,ptr,k))) = look ptr xs typ
 
subRho env (Tau x) = Tau (subTyp env x)
subRho env (Rarr s r) = Rarr(subScheme env s) (subRho env r)

subScheme env (Sch vs r) = Sch vs (subRho env r)
      
         
-}

---------------------------------------------------------------------
-- Syntax, or macro expansion works over first order terms only.
-- You cannot put a binding structure on the rhs of a syntax macro!!

showCl (Kind x) = ("kind",show x)
showCl (Type x) = ("type",show x)
showCl (Exp x)  = ("expression",show x)

unClass (Kind e) = e
unClass (Type t) = t
unClass (Exp e)  = e

returnK (Kind e) = return e
returnT (Type t) = return t
returnE (Exp e) = return e

ret f x = return(f x)

-----------------------------------------------------

type FOsub = [ (Name,Class Kind Typ Expr) ]

{-
classFind:: (FIO (Class Kind Typ Expr)) -> 
            Class Name Name Name -> 
            FOsub -> 
            FIO (Class Kind Typ Expr)
-}

classFind def x [] = def
classFind def x ((y,info):more) | unClass x /= y = classFind def x more
classFind def (Exp x) ((_,Exp t):more) = return(Exp t)
classFind def (Kind x) ((_,Kind t):more) = return(Kind t)
classFind def (Type x) ((_,Type t):more) = return(Type t)
classFind def x ((_,y):m) = fail (ycl++" variable '"++show xstr++"' used in "++xcl++" context.")
  where (xcl,xstr) = showCl x
        (ycl,_)    = showCl y
        
subKind:: FOsub -> Kind -> FIO Kind
subKind env x = do { y <- pruneK x; f y}
  where sub x = subKind env x
        f Star = return(Star)
        f (Karr x y) = liftM2 Karr (sub x) (sub y)
        f (LiftK t) = liftM LiftK (subTyp env t)
        f (k@(Kvar (uniq,ptr))) = return k
        f (Kname n) = do { Kind k <- classFind (ret Kind (Kname n)) (Kind n) env; return k}   

subTyp:: FOsub -> Typ -> FIO Typ        
subTyp env x = do { a <- prune x; f a }
  where sub x = subTyp env x
        f (TyApp g x) = liftM2 TyApp (sub g) (sub x)     
        f (typ@(TyVar s k)) =
          do { k2 <- subKind env k
             ; Type t <- classFind (ret Type (TyVar s k2)) (Type s) env; return t }             
        f (TyTuple k xs) = liftM2 TyTuple (subKind env k) (mapM sub xs)       
        f (typ@(TyCon syn c k)) = liftM (TyCon syn c) (subPolyKind env k)
        f (TyProof x y) = liftM2 TyProof (sub x) (sub y)
        f (TyArr x y) = liftM2 TyArr (sub x) (sub y)
        f (TySyn nm arity xs body) = liftM2 (TySyn nm arity) (mapM sub xs) (sub body)
        f (TyMu k) = liftM TyMu (subKind env k)        
        f (TyLift (Checked e)) = fail ("Checked expression in syntax macro expansion: "++show e)
        f (TyLift (Parsed e)) = liftM (TyLift . Parsed) (subExpr env e)
        f (TcTv (uniq,ptr,k)) = liftM (\ k -> TcTv(uniq,ptr,k)) (subKind env k)
        f (TyAll vs t) = 
	  do { (vs2,env2) <- freshTele (vs,env)
	     ; t2 <- subTyp env2 t
             ; return(TyAll vs2 t2)}   
         
subRho env (Tau t) = do {a <- subTyp env t; return(Tau a)}
subRho env (Rarr s r) = do { a <- subScheme env s; b <- subRho env r; return(Rarr a b)}

subScheme:: FOsub -> Scheme -> FIO Scheme
subScheme env (Sch vs t) = 
  do { (vs2,env2) <- freshTele (vs,env)
     ; t2 <- subRho env2 t
     ; return(Sch vs2 t2)}        

subPolyKind:: FOsub -> PolyKind -> FIO PolyKind
subPolyKind env (PolyK vs x) = 
  do { (vs2,env2) <- freshTele (vs,env)
     ; t2 <- subKind env2 x
     ; return(PolyK vs2 t2)}   

subExpr:: FOsub  -> Expr -> FIO Expr
subExpr env x = f x
   where sub x = subExpr env x
         f (ELit loc l) = return(ELit loc l)
         f (typ@(EVar s)) =
           do { Exp e <- classFind (ret Exp (EVar s)) (Exp s) env; return e }
         f (EFree s) = return(EFree s)
         f (ECon nm) = return(ECon nm)
         f (EApp x y) = liftM2 EApp (sub x) (sub y)
         f (EAbs e1 ms) = liftM2 EAbs (subElim env e1) (mapM g ms)
           where g (p,e) = 
                   do { (p2,env2) <- freshPat nameSupply (p,env)
                      ; e2 <- subExpr env2 e
                      ; return(p2,e2)}
         f (ETuple es) = liftM ETuple (mapM sub es)
         f (EIn k x) = liftM2 EIn (subKind env k) (sub x)
         f (x@(ELet d exp)) = fail ("No subExpr for (ELet _ _) yet: "++show x)
         f (x@(EMend tag e1 scr ms)) = fail ("No subExpr for (EMend _) yet: "++show x)

subElim:: FOsub -> Elim [Name] -> FIO(Elim [Name])
subElim env ElimConst = return(ElimConst)
subElim env (ElimFun xs t) = 
  do { ys <- mapM (\ n -> freshFO n env nameSupply) xs
     ; t2 <- subTyp env t
     ; return(ElimFun ys t2)}

getNamesFOsub :: FOsub -> FIO [Name]
getNamesFOsub env = foldM getname [] env
  where getname ans (nm,Kind k)   = do { (_,cl) <- getVarsKind k; return(map classToName cl ++ ans)}
        getname ans (nm,Type t)   = do { (_,cl) <- getVars t; return(map classToName cl ++ ans)}
        getname ans (nm,Exp e)    = do { (_,cl) <- getVarsE e; return(map classToName cl ++ ans)}
        
freshFO:: Name -> FOsub -> [Name] -> FIO Name
freshFO name env supply = do { bad <- getNamesFOsub env; worker name bad supply }
  where worker name bad (n:ns) = if elem name bad then worker n bad ns else return name

freshPat:: [Name] -> (Pat,FOsub) -> FIO(Pat,FOsub)
freshPat supply (PWild pos,env) = return(PWild pos,env)
freshPat supply (PLit p x,env) = return(PLit p x,env)
freshPat supply (PVar nm ty,env) = 
  do { nm2 <- freshFO nm env nameSupply
     ; return(PVar nm2 ty,(nm,Exp(EVar nm2)):env)}
freshPat supply (PTuple ps,env) =
  do { (ps2,env2) <- freshPats supply (ps,env); return(PTuple ps2,env2)}
freshPat supply (PCon nm ps,env) = 
  do { (ps2,env2) <- freshPats supply (ps,env); return(PCon nm ps2,env2)}
  

freshPats supply = threadM (freshPat supply)

freshTele:: (Telescope,FOsub) -> FIO(Telescope,FOsub)
freshTele ([],env) = return ([],env)
freshTele ((nm,Kind ()):xs,env) =   
  do { nm2 <- freshFO nm env nameSupply  
     ; let widen names = (nm,Kind(Kname nm2)):names
     ; (ys,env2) <- freshTele (xs,widen env)
     ; return((nm2,Kind ()):ys,env2)}
freshTele ((nm,Type k):xs,env) =
  do { nm2 <- freshFO nm env nameSupply  
     ; k2 <- subKind env k
     ; let widen names  = (nm,Type(TyVar nm2 k2)):names
     ; (ys,env2) <- freshTele (xs,widen env)
     ; return((nm2,Type k2):ys,env2)}
freshTele ((nm,Exp t):xs,env) =
  do { nm2 <- freshFO nm env nameSupply  
     ; t2 <- subTyp env t
     ; let widen names = (nm,Exp(EVar nm2)):names
     ; (ys,env2) <- freshTele (xs,widen env)
     ; return((nm2,Exp t2):ys,env2)}    
     
-------------------------------------------------------------------------
-- All the TEqual stuff
-------------------------------------------------------------------------

zonkTEqual x = do { y <- pruneTEqual x; zonkEq y } where
  zonkEq (TRefl t) = liftM TRefl (zonk t) 
  zonkEq (TCong x y) = liftM2 TCong (zonkTEqual x) (zonkTEqual y)
  zonkEq (TProofCong x y) = liftM2 TProofCong (zonkTEqual x) (zonkTEqual y)
  zonkEq (TComp x y) = liftM2 TComp (zonkTEqual x) (zonkTEqual y)
  zonkEq (TJoin x) = liftM TJoin (zonkExp x)
  zonkEq (TArrCong x y) = liftM2 TArrCong (zonkTEqual x) (zonkTEqual y)
  zonkEq (TTupleCong xs) = liftM TTupleCong (mapM zonkTEqual xs)
  zonkEq (TSpec sch ts) = liftM2 TSpec (zonk sch) (mapM zonk ts)
  zonkEq (TGen b x) = liftM2 TGen (mapM zonkClass b) (zonkTEqual x)
  zonkEq (TVar p) = return(TVar p)
  zonkEq (TSym x) = liftM TSym (zonkTEqual x)
 
  
getVarsTEqual:: TEqual -> FIO Vars
getVarsTEqual (TRefl t) = getVars t
getVarsTEqual (TCong x y) =
          do { trip1 <- getVarsTEqual x 
             ; trip2 <- getVarsTEqual y
             ; (unionW trip1 trip2)}
getVarsTEqual (TProofCong x y) =
          do { trip1 <- getVarsTEqual x 
             ; trip2 <- getVarsTEqual y
             ; (unionW trip1 trip2)}
getVarsTEqual (TComp x y) =
          do { trip1 <- getVarsTEqual x 
             ; trip2 <- getVarsTEqual y
             ; (unionW trip1 trip2)}             
getVarsTEqual (TJoin x) = getVarsExpr x             
getVarsTEqual (TArrCong x y) =
          do { trip1 <- getVarsTEqual x 
             ; trip2 <- getVarsTEqual y
             ; (unionW trip1 trip2)}             
getVarsTEqual (TTupleCong xs) = foldM (accumBy getVarsTEqual) ([],[]) xs  
getVarsTEqual (TSpec sch xs) = 
  do { trip1 <- getVars sch
     ; trip2 <- foldM (accumBy getVars) ([],[]) xs  
     ; unionW trip1 trip2 }
getVarsTEqual (p@(TGen sch xs)) = error ("There should be no embedded TGen, Should be handled in the TECast case of getVarsExpr: "++show p)
getVarsTEqual (TVar x) = return([],[]) 
getVarsTEqual (TSym x) = getVarsTEqual x  


eqSubb::  SourcePos -> SubEnv -> TEqual -> FIO TEqual
eqSubb pos env (TRefl x) = liftM TRefl (tySubb pos env x)
eqSubb pos env (TCong x y) = liftM2 TCong (eqSubb pos env x)(eqSubb pos env y)  
eqSubb pos env (TProofCong x y) = liftM2 TProofCong (eqSubb pos env x)(eqSubb pos env y)  
eqSubb pos env (TComp x y) = liftM2 TComp(eqSubb pos env x)(eqSubb pos env y)  
eqSubb pos env (TJoin x) = liftM TJoin(expSubb pos env x) 
eqSubb pos env (TArrCong x y) = liftM2 TArrCong (eqSubb pos env x)(eqSubb pos env y)       
eqSubb pos env (TTupleCong xs) = liftM TTupleCong (mapM (eqSubb pos env) xs)
eqSubb pos env (TSpec sch xs) = liftM2 TSpec (tySubb pos env sch) (mapM (tySubb pos env) xs)
eqSubb pos env (p@(TGen sch xs)) = error ("There should be no embedded TGen, Should be handled in the TECast case of exprSubb: "++show p)
eqSubb pos env (TVar x) = return(TVar x)
eqSubb pos env (TSym x) = liftM TSym (eqSubb pos env x)
     
--------------------------------------------------------------------------   

unifyT:: SourcePos -> [String] -> Variance -> Typ -> Typ -> FIO(TEqual)
unifyT loc mess variance x y = do { x1 <- prune x; y1 <- prune y
                   --  ; writeln("\nUnify "++show variance++" "++show x1++" =?= "++show y1)
                       ; f x1 y1 } where 
  f (t1@(TyVar n k)) (TyVar n1 k1) | n==n1 =
      do { unifyK noPos mess k k1; return(tRefl t1)}
  f (TyApp x y) (TyApp a b) = 
      do { c1 <- unifyT loc mess variance x a
         ; kind <- kindOf x
         ; c2 <- case kind of
                   -- Karr (k1,Neg) k2 ->  unifyT mess (flipVar variance ) y b
                   any  {- Karr (k1,Pos) k2 -} ->  unifyT loc mess variance y b
                   -- Karr (k1,Both) k2 -> unifyT mess Both y b
         ; return(tCong c1 c2)}
  f (TyTuple _ xs) (TyTuple _ ys) 
    | length xs == length ys 
    = do { cs <- sequence(zipWith (unifyT loc mess variance) xs ys); return(tTupleCong cs)}
  f (t1@(TyCon _ n _)) (TyCon _ m _) | n==m = return(tRefl t1)
  f (t1@(TcTv (_,p1,_))) (t2@(TcTv (_,p2,_))) | p1==p2 = return(tRefl t1)
  f (TyProof x y) (TyProof a b) =
        do { p1 <- unifyT loc mess variance x a
           ; p2 <- unifyT loc mess variance y b 
           ; return(tProof p1 p2)}
  f (TySyn n1 a1 xs1 b1) x = unifyT loc mess variance b1 x
  f y (TySyn n2 a2 xs2 b2) = unifyT loc mess variance y b2 
  f (t@(TyMu k1)) (TyMu k2) = unifyK loc mess k1 k2 >> return(tRefl t)
  f (TyArr x y) (TyArr a b) = 
      do { c1 <- unifyT loc mess (flipVar variance ) x a
         ; c2 <- unifyT loc mess variance y b
         ; return(tArrCong c1 c2)}       
  f (TyLift (Checked e)) (TyLift (Checked g)) = 
    do { (writeln ("\n*****\nIn UnifyT Normalizing\n Handle TEqual for normlization\n  "++
                   show e++", "++show g))
       ; ez <- zonkExp e  
       ; gz <- zonkExp g  
       ; writeln("After zonk "++show ez++", "++show gz)
       ; enf <- normform ez
       ; gnf <- normform gz
       ; writeln("After norm "++show enf++", "++show gnf)       
     
       ; e <- unifyExpT loc mess enf gnf     
       ; if nosplit e
            then return (tRefl(TyLift (Checked e)))
            else return (TJoin e) }
  f (TyLift (Parsed e)) _ = error ("unchecked term in type inside unify: "++show e)
  f _ (TyLift (Parsed e)) = error ("unchecked term in type inside unify: "++show e)
--  f (TyLift (Pattern e)) _ = error ("unchecked term in type inside unify: "++show e)
--  f _ (TyLift (Pattern e)) = error ("unchecked term in type inside unify: "++show e)   
  f (TyAll vs t) (TyAll us s) = error ("No TyAll in unifyT yet")
  f (TcTv x) t2 = unifyVar loc mess x t2 >> return (tRefl t2)
  f t2 (TcTv x) = unifyVar loc mess x t2 >> return (tRefl t2)
  f x y = matchErr loc mess x y  
 
-----------------------------------------------------------------
-- Checking that one type is more polymorphic than another

-- unifyFun t -----> (a,b,p)  then  p means  t => (a -> b)

unifyFunT :: SourcePos -> [String] -> Rho -> FIO(Scheme,Rho,TEqual)
unifyFunT loc mess (r@(Rarr x y)) = return (x,y,TRefl (rhoToTyp r))
unifyFunT loc mess (Tau (t@(TyArr x y))) = return(Sch [] (Tau x),Tau y,tRefl t)
unifyFunT loc mess (Tau x) =
   do { a <- freshType Star
      ; b <- freshType Star
      ; p <- unifyT loc ("\nIn unifyFun" : mess) Pos x (arrT a b)
      ; a1 <- zonk a
      ; b1 <- zonk b
      ; return (Sch [] (Tau a1),Tau b1,p) }  
           

-- morpolySRT x y ---> p   p means x => y
      
morepolySRT:: SourcePos -> [String] -> Scheme -> Rho -> FIO ([Typ],TEqual)
morepolySRT loc mess (Sch [] rho1) rho2 =  
   do { p <- morepolyRRT loc mess rho1 rho2; return ([],p) }
morepolySRT loc mess sigma1 rho2 =
     do { (rho1,newts) <- instantiate sigma1
        ; p <- morepolyRRT loc mess rho1 rho2
        ; return(newts,TComp (tSpec sigma1 newts) p)
        }

-- morpolyRRT x y ---> p   p means x => y

morepolyRRT:: SourcePos -> [String] -> Rho -> Rho -> FIO TEqual
morepolyRRT loc mess x y = f x y where
  f (Rarr a b) x = do{(m,n,p1) <- unifyFunT loc mess x
                     ; p2 <- morepolyRRT loc mess b n
                     ; p3 <- morepolySST loc mess m a 
                     ; return(tComp (tArrCong (tSym p3) p2) p1)}
  f x (Rarr m n) = do{(a,b,p1) <- unifyFunT loc mess x
                     ; p2 <- morepolyRRT loc mess b n
                     ; p3 <- morepolySST loc mess m a
                     ; return(tComp p1 (tArrCong (tSym p3) p2))}
  f (Tau x) (Tau y) = unifyT loc mess Pos x y


morepolySST:: SourcePos -> [String] -> Scheme -> Scheme -> FIO TEqual
morepolySST loc mess sigma1 (Sch [] rho) =  
  do { (ts,p) <- morepolySRT loc mess sigma1 rho; return p }
 
morepolySST loc mess sigma1 sigma2 =
  do { (skol_tvs,ts1,rho) <- rigidize sigma2
     ; let p1 = tSpec sigma2 ts1
     ; (t2s,p2) <- morepolySRT loc mess sigma1 rho
   --  ; (_, tv1,_,_) <- get_tvsScheme sigma1   
   --  ; (_, tv2,_,_) <- get_tvsScheme sigma2 
     ; (ptrs1,names1) <- getVarsScheme sigma1
     ; (ptrs2,names2) <- getVarsScheme sigma2
     ; let tv1 = foldr typeAccDrop [] names1
           tv2 = foldr typeAccDrop [] names2
           esc_tvs = tv1++tv2
           bad_tvs = filter (`elem` esc_tvs) skol_tvs
     ; case bad_tvs of
         [] -> return (tComp p2 (tSym p1))
         zs -> fail (unlines(("\nVars escape in morepolySS: "++show bad_tvs):mess))
     }
   
{- Impredicative form
unifyFun mess x = do { x2 <- pruneTyp x; help mess x2 }
  where help mess (t@(TyArr dom rng)) = return(dom,rng,TRefl t)
        help mess (t@(TyAll ds body)) = 
           do { (p1,body2) <- instanGen t
              ; (dom,rng,p2) <- unifyFun mess body2
              ; return(dom,rng,tComp p1 p2)}
        help mess (t@(TcTv r)) =
           do { dom <- freshTyp Star
              ; rng <- freshTyp Star
              ; p <- unifyT mess Both t (TyArr dom rng)
              ; return(dom,rng,p)}
        help mess t = matchErr (("Not a function type: "++show t) : mess)
-}        