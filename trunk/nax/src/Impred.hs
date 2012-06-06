{-# LANGUAGE GADTs, FlexibleInstances, TypeSynonymInstances, TupleSections #-}

module Impred where


-- What is the story about scoped type variables?
-- types in patterns?

import Names

import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

import qualified System.IO
import qualified System.IO.Error
import Data.List(groupBy,union,(\\),intersect)

import Data.Char(digitToInt,isUpper)

-- These are for defining parsers
import Text.Parsec  
import Text.Parsec.Language(javaStyle,haskellStyle)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import Language.Trellys.LayoutToken -- Replaces Text.Parsec.Token
                   -- and adds layout rule parsing capability
                   
import Monads(FIO(..),handle,runFIO,fio,nextInteger,writeln
             ,unionByM,lift1,lift2,lift3,lift4,when,anyM
             ,newRef,writeRef,readRef,failFIOwith,handleP
             )
             
import Debug.Trace             
---------------------------------------------------------
-- Pointers

type Pointer t = IORef (Maybe t)
type Uniq = Integer

-----------------------------------------------------------
-- Kinds 

data Variance = Pos | Neg | Both 

data Kind   
   = Star 
   | Karr (Kind,Variance) Kind
   | Kvar (Uniq,Pointer Kind)
   | Kname Name


data PKind
  = PStar
  | PKarr PKind PKind
  | PIndex PTyp PKind
  | PName Name
  
---------------------------------------
-- Patterns

data Pat n t
   = PLit SourcePos (Either Int Char)
   | PVar n
   | PCon Name [Pat n t]
   | PWild SourcePos
   | PTyp (Pat n t) t


---------------------------------------
-- Parsed  things

data Expr
   = ELit SourcePos (Either Int Char)
   | EVar Name        
   | EApp Expr Expr                                   
   | EAbs (Pat Name PTyp) Expr
   | ETuple [Expr]
   | ELet (Decl Name Expr (Maybe (SourcePos,PTyp))) Expr
   | ECase Expr [(Pat Name PTyp,Expr)]
   | EPolyStar Expr  -- (Maybe PTyp)
   | Epoly [Name] Expr PTyp
   | EInst Expr (Maybe PTyp)

data Decl nm e t = Intro SourcePos t nm e | TypeSig SourcePos nm PTyp
   
data PTyp 
   = PTyVar Name
   | PTyApp PTyp PTyp
   | PTyArr PTyp PTyp
   | PTyTuple [PTyp]
   | PTyCon Name 
   | PTyAll [Name] PTyp 

   
--------------------------------------------
-- Typed things

type Var = (Name,Typ)

data TExpr   
   = TELit SourcePos (Either Int Char)
   | TEVar Var
   | TEApp TExpr TExpr                                   
   | TEAbs (Pat Var Typ) TExpr
   | TETuple [TExpr]
   | TELet (Decl Var TExpr Typ) TExpr
   | TECase TExpr [(Pat Var Typ,TExpr)]   
   | TECast TEqual TExpr
   
data Fomega  
   = FLit SourcePos (Either Int Char)
   | FVar Var
   | FApp Fomega Fomega                                   
   | FAbs (Pat Var Typ) Fomega
   | FLet (Decl Var Fomega Typ) Fomega
   | FCase Fomega [(Pat Var Typ,Fomega)] 
   | FTuple [Fomega]
   | FTypApp Fomega [Typ]
   | FTypAbs [Bind] Fomega
   | FCast Typ Typ Fomega
   
    
data Typ 
   = TyVar (Name,Kind)
   | TyApp Typ Typ
   | TyArr Typ Typ
   | TyTuple [Typ]
   | TyCon Name Kind
   | TyAll [Bind] Typ
   | TcTv (Uniq,Pointer Typ,Kind)
--    | TyCast Coercion Typ


-----------------------------------------------------------

data Tree a 
    = Fail String 
    | One a 
    | Choice [PSub] [(Typ,Typ,Int,TEqual)] [FIO(Tree a)]

disptree :: Int -> Int -> ([PSub] -> Doc) -> Tree [PSub] -> FIO Doc
disptree d n f x | d > 6 = return(PP.nest n (text "..."))
disptree d n f (Fail s) = return(PP.nest n (text ("FAIL "++s)))
disptree d n f (One x) = return (PP.nest n (text "SOLUTION" <> f x))
disptree d n f (Choice sub ys ts) = 
  do { zs <- mapM id ts
     ; ds <- mapM (disptree (d+1) (n+3) f) zs
     ; return(PP.vcat (PP.nest n (text "CHOICE ")<> f sub : 
                       PP.nest n (ppInput pi0 ys) : ds)) }

ppInput p xs = PP.sep(map f xs)
  where f (t1,t2,n,proof) = PP.parens(ppTyp p t1<> text ","<> ppTyp p t2<>text "," <> text(show n))

filterTree p (Fail s) = return (Fail s)
filterTree p (One x) = return(One x)
filterTree p (Choice x ys ts) = do { bool <- p x; test bool }
  where test True = return(Choice x ys (map f ts))
        test False = return (Fail "filter failure")
        f t = do { tree <- t; filterTree p tree}

bfs :: [Tree a] -> FIO [a]
bfs [] = return []
bfs (Fail s : more) = bfs more
bfs (One x : more) = lift1 (x :) (bfs more)
bfs (Choice x ys ts : more) = 
  do { ms <- mapM id ts; bfs(more ++ ms)}


subL :: ([Sub], [PSub]) -> [(Typ,Typ,Int,TEqual)] -> FIO [(Typ,Typ,Int,TEqual)]
subL sub [] = return[]
subL sub (x : xs) = lift2 (:) (one x) (subL sub xs)
   where one (x,y,n,p) = lift4 (,,,) (subbTyp sub x) (subbTyp sub y) (return n) (return p)

compose:: [PSub] -> [PSub] -> FIO [PSub]
compose xs ys = do { zs <- (mapM f ys); return(zs++xs)}
  where f (ExprPS p e) = lift1 (ExprPS p) (subbTExpr ([],xs) e)
        f (TypePS p t) = lift1 (TypePS p) (subbTyp  ([],xs) t)
        f (KindPS p k) = lift1 (KindPS p) (subbKind ([],xs) k)

   
solve:: [PSub] -> [(Typ,Typ,Int,TEqual)] -> FIO (Tree [PSub])
solve sub [] = return(One sub)
solve sub ((x,w,n,p):more) | n > 2 = return (Fail "depth")
solve sub (x:more) =
  case x of 
    (TyVar (n,_),TyVar (m,_),_,p) | n==m -> solve sub more                       
    (TyApp t x,TyApp s y,n,p) -> 
      do { p1 <- freshTEqual; p2 <- freshTEqual; solve sub ((t,s,n,p1):(x,y,n,p2):more) }
    (TyArr t x,TyArr s y,n,p) -> 
      do { p1 <- freshTEqual; p2 <- freshTEqual; solve sub ((s,t,n,p1):(x,y,n,p2):more) }
    (TyCon n _,TyCon m _,_,p) | n==m -> solve sub more    
    (t1@(TyAll bs t),t2@(TyAll cs s),n,p) -> 
      do { (skol,skTy) <- skolem cs s
         ; (_,genproof,freshTy) <- instanGen t1
         ; (ptrs,names2) <- getVarsTyp t1
         ; let free = map unPtr ptrs
               good u x = (not(elem u free)) || (not(elem (unName x) skol))
         ; tree <- solve sub ((freshTy,skTy,n,p):more)
         ; let p sub = anyM escape sub
               escape (TypePS (u,p,k) t) = do { (ps,ns) <- getVarsTyp t ; return(all (good u) ns)}
               escape (KindPS (u,p) k)   = do { (ps,ns) <- getVarsKind k; return(all (good u) ns)}
               escape (ExprPS (u,p,t) e) = do { (ps,ns) <- getVarsExpr e; return(all (good u) ns)}
         ; filterTree p tree } 
    (TyTuple xs,TyTuple ys,n,p) | length xs == length ys -> solve sub (foldr acc more (zip xs ys))
       where acc (x,y) ans = (x,y,n,p):ans
    (t1@(TyAll bs t),w@(TcTv v),n,p) -> return(Choice sub (x:more) [instan,pick,defer])
      where instan = 
              do { (_,genproof,freshTy) <- instanGen t1
                 ; solve sub ((freshTy,w,n,p):more) }
            pick = 
              do { sub2 <- compose [TypePS v t1] sub
	         ; more2 <- subL ([],sub2) more
	         ; solve sub2 more2 }
            defer = solve sub (more ++ [(TcTv v,w,n+1,p)])
    (t1@(TyAll bs t),w,n,p) -> 
      do { (_,genproof,freshTy) <- instanGen t1
         ; solve sub ((freshTy,w,n,p):more)  }          
    (w,TcTv v,n,p) -> 
      do { sub2 <- compose [TypePS v w] sub
         ; more2 <- subL ([],sub2) more
         ; solve sub2 more2 }
    (TcTv v,w,n,p) -> 
         return(Choice sub (x:more) [pick,defer])
      where pick = do { sub2 <- compose [TypePS v w] sub
                      ; more2 <- subL ([],sub2) more
                      ; solve sub2 more2 }
            defer = solve sub (more ++ [(TcTv v,w,n+1,p)])             
    (x,y,n,p) -> return (Fail ("NO MATCH "++show x++" =/= "++show y))

-- after solving, we might want to propogate the information from
-- the pure substitution to the statefull IORef substitution

pushSol (TypePS p t) = unifyT [] Pos (TcTv p) t
pushSol (KindPS p k) = fail ("no KindPS in pushSol")
pushSol (ExprPS p e) = fail ("no ExprPS in pushSol")


-------------------------------------------------

instance Eq Typ where
 (TyVar (n,_)) == (TyVar (m,_)) = n==m
 (TyApp f x) == (TyApp g y) = f==g && x==y
 (TyArr f x) == (TyArr g y) = f==g && x==y 
 (TyTuple xs) == (TyTuple ys) = xs==ys
 (TyCon n _) == (TyCon m _) = n==m
 (TcTv (u1,_,_)) == (TcTv (u2,_,_)) = u1 == u2
 (TyAll bs t) == (TyAll cs s) = same bs cs && t==s
   where same [][] = True
         same (x:xs)(y:ys) = ok x y && same xs ys
         same _ _ = False
         ok (TypeB n _) (TypeB m _) = n==m
         ok (ExprB n _) (ExprB m _) = n==m
         ok (KindB n ) (KindB m) = n==m
         ok _ _ = False
 x == y = False
 
       

-------------------------------------------------------
-- Coercion evidence

data VarianceLift = VRefl Variance | PosLift | NegLift

data KEqual
  = KRefl Kind
  | KArrCong (KEqual,VarianceLift) KEqual
    
data TEqual where
  TRefl :: Typ -> TEqual
  TCong:: TEqual -> TEqual -> TEqual   --  App:: (f >= g) (x >= y) -> (f x) >= (g y)  | positive f g
  TArrCong:: TEqual -> TEqual -> TEqual 
  TTupleCong:: [TEqual] -> TEqual
  TSpec:: Typ -> [Sub] -> Typ -> TEqual
  TGen:: [Bind] -> TEqual -> TEqual
  TVar:: (Uniq,Pointer TEqual) -> TEqual
  -- we don't use these in type inference
  TVarLift:: (Name,KEqual) -> TEqual
  TComp:: TEqual -> TEqual -> TEqual
  TSym:: TEqual -> TEqual


type Const = [(Name,Typ,[(Typ,TEqual)])]
type Constraints = (Const,Const)

addCon:: Name -> (Typ,TEqual) -> Constraints -> FIO Constraints
addCon nm pair (cs,ds) = do { es <- push cs; return(es,ds) }
  where push [] = fail ("Variable not found: "++show nm++" while adding Constraints.")
        push ((name,t,ps):xs) | nm==name = return((name,t,pair:ps):xs)
        push (x:xs) = do { ys <- push xs; return(x:ys)}
  
push:: Name -> Typ -> Constraints -> Constraints  
push nm typ (cs,ds) = ((nm,typ,[]):cs,ds)

pop :: Constraints -> Constraints
pop (c:cs,ds) = (cs,c:ds)

pushFrag :: Frag -> Constraints -> Constraints
pushFrag (ts,es) (cs,ds) = (foldr acc cs es,ds)
  where acc (nm,(t,Bullet)) cs = ((nm,t,[]):cs)
        acc (nm,(t,Asterix)) cs = cs
        
popFrag :: Frag -> Constraints -> Constraints
popFrag (ts,es) cs = (foldr acc cs es)
  where acc (nm,(t,Bullet)) (c:cs,ds) = (cs,c:ds)
        acc (nm,(t,Asterix)) cs = cs        

-----------------------------------------------------------            
-- Values and environments

data Value 
   = VLit (Either Int Char)
   | VCon String [Value]
   | VFun (Value -> Value)

data GenPoint = Asterix | Bullet
lub Asterix Asterix = Asterix
lub _ _ = Bullet


instance Show GenPoint where
  show Asterix = "I"
  show Bullet = "G"

data Env = Env { tcon ::  [(Name,Schema Kind)]
               , tvar ::  [(Name,(Typ,Kind))]  
               , evar ::  [(Name,(Typ,GenPoint))]
               , lamBnd::  [(Name,Typ)] -- A subset of evar
               , runtime:: [(Name,Value)]
               }

envStar env = env{evar = filter p (evar env)}
  where p (nm,(t,Asterix)) = True
        p (nm,(t,Bullet)) = False

--------------------------------------------------------
-- we want these types to be predefined

-- data Maybe a = Nothing | Just a,      Maybe:: (*,+) -> *
-- data Bool = True | False              Bool:: *
-- data List a = Nil | Cons a (List a),  List::  (*,+) -> *
-- data Show a = Show (a -> List Char),  Show::  (*,-) -> *
-- data Closure t a = Close (t -> a) t,  Closure:: (*,?) -> (*,+) -> *
-- data Pair x y = P x y                 Pair:: (*,+) -> (*,+) -> *

conTyp s k = TyCon (toName s) k -- (Poly [] k)

intT = conTyp "Int" Star
charT = conTyp "Char" Star
maybeT = conTyp "Maybe" (Karr (Star,Pos) Star)
boolT = conTyp "Bool" Star
listT = conTyp "List" (Karr (Star,Pos) Star)
showT = conTyp "Show" (Karr (Star,Neg) Star)
closureT = conTyp "Closure" (Karr (Star,Both) (Karr (Star,Pos) Star))
pairT = conTyp "Pair" (Karr (Star,Pos) (Karr (Star,Pos) Star))
monadT = conTyp "Monad" (Karr (Karr (Star,Both) Star,Both) Star)

tycon0 = map f [intT,charT,maybeT,boolT,listT,showT,closureT,pairT,monadT]
  where f (TyCon nm pk) =(nm,(Poly [] pk))

constructors = 
  [("Nothing", "(forall a . Maybe a)",VCon "Nothing" [])
  ,("Just", "(forall a . a -> Maybe a)",VFun (\ v -> VCon "just" [v]))
  ,("True", "(forall . Bool)",VCon "True" [])
  ,("False", "(forall . Bool)",VCon "False" [])
  ,("Nil", "(forall a . List a)",VCon "Nil" [])
  ,("Cons", "(forall a . a -> List a -> List a)",VFun( \ x -> VFun( \ y -> VCon "Cons" [x,y])))
  ,("Show", "(forall a. (a -> List Char) -> Show a)",VFun(\ x -> VCon "Show" [x]))
  ,("Close", "(forall t a . (t -> a) -> t -> Closure t a)",VFun( \ x -> VFun( \ y -> VCon "Close" [x,y])))
  ,("P", "(forall a b . a -> b -> Pair a b)",VFun( \ x -> VFun( \ y -> VCon "P" [x,y])))
  ,("Mon","(forall m . (forall a . a -> m a) -> (forall a b . m a -> (a -> m b) -> m b) -> Monad m)",VLit (Left 4))

  ]

env0 = Env tycon0 [] [] [] (map (\ (nm,t,v)-> (toName nm,v)) constructors)               
initialEnvs = do { evar0 <- mapM f constructors; return(env0{evar = evar0})}
 where f (nm,str,v) = do { (t,k) <- wellFormedType ["Initializing"] env0 (parse2 typP str)
                         ; t2 <- zonkTyp t
                         ; return(toName nm,(t2,Asterix))}

-----------------------------------------------------------------

wellFormedType:: [String] -> Env -> PTyp -> FIO(Typ,Kind)
wellFormedType mess env typ = do { f2 <- zonkEnv env; f f2 typ }
  where has frag k1 x = 
           do { (x2,k2) <- wellFormedType mess frag x
              ; unifyK (("checking term ("++show x2++": "++show k2++") has expected kind:"++show k1):mess) k2 k1
              ; return x2 }                       
        f frag (PTyVar nm) | name nm == "_" =
           do { k <- freshKind; t <- freshTyp k; return(t,k)}
        f frag (PTyVar nm) = 
           case lookup nm (tvar frag) of
              Just pair -> return pair
              other -> fail(near nm ++ "Type variable: "++show nm++", not in scope.")    
        f frag (PTyApp fun x) = 
          do { dom <- freshKind; rng <- freshKind
             ; (f2,k2) <- wellFormedType mess frag fun 
             ; p1 <- unifyK mess k2 (Karr (dom,Pos) rng)
             ; x2 <- has frag dom x
             ; return(TyApp f2 x2,rng)}
        f frag (PTyArr x y) = 
            do { x2 <- has frag Star x; y2 <- has frag Star y; return(TyArr x2 y2,Star)}             
        f frag (PTyCon c) =
           case lookup c (tcon frag) of
             Just pk -> do { k <- instanPoly subbKind pk; return(TyCon c k,k) }
             other -> fail(near c ++ "Unknown type constuctor: "++show c) 
        f frag (PTyTuple xs) = 
          do { ys <- mapM (has frag Star) xs; return(TyTuple ys,Star)}
        f frag (PTyAll ns t) = 
          do { let f nm = lift1 (h nm) freshKind 
                   h nm k = (nm,(TyVar (nm,k),k))
                   g (nm,(t,k)) = TypeB nm k
             ; delta <- mapM f ns
             ; let env2 = frag {tvar= delta ++ (tvar frag)}
             ; (t2,k2) <- wellFormedType mess env2 t
             ; return(TyAll (map g delta) t2,k2)}
             
-- Computes the kind of a wellFormedType.
kindOf:: Typ -> FIO Kind
kindOf (TyVar (nm,k)) = pruneK k
kindOf (typ@(TyApp t x)) = 
  do { kt <- kindOf t
     ; kx <- kindOf x
     ; case kt of
        (Karr (k1,v) k2) ->  -- we probably can just return k2, if the type really is well-formed
           do { unifyK ["In kindOf "++show typ++"\n  "++showPair(t,kt)++"\n  "++showPair(x,kx)] k1 kx
              ; pruneK k2 }
        k -> fail ("Type construtor: "++show t++" does not have an arrow kind: "++show k)}
kindOf (TyArr x y) = return Star
kindOf (TyCon nm sch) = pruneK sch  -- TyCon are instantiated in wellFormedType and carry mono types
kindOf (TyAll bs t) = kindOf t
kindOf (TcTv(uniq,ptr,k)) = pruneK k             

----------------------------------------------------
-- First some data structures to encode the environment

data Expected t = Check t | Infer (IORef t)

zonkExpect (Check t) = lift1 Check (zonkTyp t)
zonkExpect (Infer ref) = return(Infer ref)

instance Show t => Show (Expected t) where
  show (Check t) = show t
  show (Infer ref) = "infer"

type Frag = ([(Name,(Typ,Kind))],[(Name,(Typ,GenPoint))])

addTermVar v (sigma@(TyAll _ _)) (ts,es) = (ts,(v,(sigma,Asterix)):es)
addTermVar v sigma (ts,es) = (ts,(v,(sigma,Bullet)):es)

addTypVar (TypeS nm t k) (ts,es) = ((nm,(t,k)):ts,es)
addTypVar (ExprS nm e t) (ts,es) = (ts,(nm,t):es)
addTypVar (KindS nm k)   (ts,es) = (ts,es)


------------------------------------------------------------
-- Type Checking
------------------------------------------------------------

castArg (x,Nothing) = return x
castArg (x,Just(t1,t2)) | t1==t2 = return x
castArg (x,Just(t1@(TyAll _ _),t2)) = 
   do { (ts,genproof,t3) <- instanGen t1
      ; p <- unifyT [] Pos t2 t3
      ; zonkFomega (FTypApp x ts)}
castArg (x,Just(t1,t2)) = error ("uncast arg "++show x++"Actual "++show t1++" Needed "++show t2)

castFun (f,Nothing) x = return(FApp f x,Nothing)
castFun (f,Just(t1,t2))x | t1==t2 = return(FApp f x,Nothing)
castFun (f,Just(TyArr a b,TyArr c d)) x | a==c = return(FApp f x,Just(b,d))
castFun (f,Just(t1@(TyAll _ _),t2)) x = 
   do { (ts,genproof,t3) <- instanGen t1
      ; p <- unifyT [] Pos t2 t3
      ; lift1 (,Nothing) (zonkFomega (FApp (FTypApp f ts) x))}
castFun (f,Just(t1,t2)) x = error ("uncast fun "++show (FApp f x)++"\nActual "++show t1++"\nNeeded "++show t2)
      

uncast:: Fomega -> FIO(Fomega,Maybe(Typ,Typ))
uncast (FCast t1 t2 t) = do { s1 <- zonkTyp t1; s2 <- zonkTyp t2
                            ; return(t,Just(s1,s2)) }
uncast (FLit p x) = return(FLit p x,Nothing)
uncast (FVar v) = return(FVar v,Nothing)
uncast (FApp f x) = 
  do { infof <- uncast f
     ; infox <- uncast x
     ; y <- castArg infox
     ; castFun infof y }
uncast (FAbs pat body) = 
  do { infob <- uncast body
     ; case infob of
         (b,Nothing) -> return(FAbs pat b,Nothing)
         (b,Just(t1,t2)) | t1==t2 -> return(FAbs pat b,Nothing)
         (b,Just(t1,t2)) -> error ("uncast Abs "++show b++"Actual "++show t1++" Needed "++show t2)
     }
uncast (FTuple es) = 
  do { infos <- mapM uncast es
     ; let combine (x,Nothing) = return x
           combine (x,Just(t1,t2)) | t1==t2 = return x
           combine (x,Just(t1,t2)) = fail ("uncast Tuple element "++show x++"Actual "++show t1++" Needed "++show t2)
     ; xs <- mapM combine infos
     ; return(FTuple xs,Nothing) }
uncast (FTypAbs bs e) = 
  do { infob <- uncast e
     ; case infob of
         (b,Nothing) -> return(FTypAbs bs b,Nothing)
         (b,Just(t1,t2)) | t1 == t2 -> return(FTypAbs bs b,Nothing)
         (b,Just(t1,t2)) -> error ("uncast FTyAbs "++show b++"Actual "++show t1++" Needed "++show t2)}
uncast (FTypApp e ts) = 
  do { infob <- uncast e
     ; case infob of
         (b,Nothing) -> return(FTypApp b ts,Nothing)
         (b,Just(t1,t2)) | t1 == t2 -> return(FTypApp b ts,Nothing)
         (b,Just(t1,t2)) -> error ("uncast FTypApp "++show b++"Actual "++show t1++" Needed "++show t2)}

uncast x = error ("Not yet in uncast\n"++show x)         



inferFomega :: [String] -> Env -> Constraints -> Expr -> FIO (Typ,Fomega,Constraints)
inferFomega mess env cs e = 
  do { r <- fio(newIORef (TyVar (Nm("?",noPos),Star)))
     ; (e',ds) <- typeFomega mess env cs e (Infer r)
     ; rho <- fio (readIORef r)
     ; lift1 (,e',ds) (pruneTyp rho) }
                                  
                                  
fTypApp x [] = x
fTypApp x bs = FTypApp x bs
fTypAbs [] e = e
fTypAbs bs e = FTypAbs bs e



typeFomega:: [String] -> Env -> Constraints -> Expr -> Expected Typ -> FIO(Fomega,Constraints)
typeFomega mess env cs e expect = -- writeln("\nTypeExp "++show e++" : "++show expect) >>
  case e of
    ELit pos c -> 
      do { let typeOf (Left n) = intT
               typeOf (Right c) = charT
         ; p <- unifyExpect mess (typeOf c) expect
         ; return(FLit pos c,cs) }  
    EVar nm -> 
      case lookup nm (evar env) of
        Just (t,Asterix) ->  
           do { (ts,genproof,t3) <- instanGen t
              ; p <- unifyExpect mess t3 expect
              ; return(fTypApp (FVar (nm,t)) ts,cs)} 
        Just(t,Bullet) -> 
           do { let fresh (Check t) = return t
                    fresh (Infer ref) = do { t <- freshTyp Star; fio(writeIORef ref t); return t}
              ; alpha <- fresh expect
              ; p1 <- freshTEqual
              -- ; writeln("\n-----------\nTypeExp Var Bullet case "++show e++"\nexpect   "++show alpha++"\n actual "++show t)
              ; cs2 <- addCon nm (alpha,p1) cs
              -- in a second pass (uncast) we resolve the differences between t and alpha
              ; return(FCast t alpha (FVar (nm,t)),cs2) } 
        Nothing -> failFIOwith (loc nm) 5 "NotInScope" (show nm ++ " not in scope.")         
    (EApp f x) ->
      do { (t,f2,cs2) <- inferFomega mess env cs f
         ; (dom,rng,p1,ts) <- unifyFun (("While checking the application\n   "++ show e++"\nhas type "++show expect):mess) t
         ; (x2,cs3) <- typeFomega (("While checking the argument\n   "++show x++"\nhas type "++show dom++"\nin the application\n   "++show e):mess)
                           env cs2 x (Check dom)
         -- ; when (genVar env f && (not (mono p1)))
         --       (matchErr((near f++"Lambda bound variable used at more than one type "++show p1++"\n "++show f++" (case 2)"):mess))
         ; p2 <- unifyExpect mess rng expect         
         ; return(FApp (fTypApp f2 ts) x2,cs3) }    
    (term@(EAbs p body)) ->
      case expect of
        Check (TyAll bs t) -> 
          do { -- writeln("\nTyAll case of EAbs\n  "++show expect);
               (exp2,cs2) <- typeFomega mess env cs (EAbs p body) (Check t)               
             ; p <- escapeTyAllCheck mess env bs expect e (TRefl t)
             ; return(FTypAbs bs exp2,cs2)}                                              
        Check t ->
          do { (dom,rng,p1,ts) <- unifyFun mess t  -- t is not TyAll, so ts must be []
             ; (p2,frag) <- bindPat env ((dom,p),([],[]))
             ; (body2,cs2) <- typeFomega mess (extendPatEnv env frag) (pushFrag frag cs) body (Check rng)
            -- ; let ans = (teCast (tSym p1) (TEAbs p2 body2))
             ; return(FAbs p2 body2,popFrag frag cs2)}
        Infer ref ->
          do { dom <- freshTyp Star
             ; (p2,frag) <- bindPat env ((dom,p),([],[]))
	     ; (rng,body2,cs2) <- inferFomega mess (extendPatEnv env frag) (pushFrag frag cs) body
             ; fio(writeIORef ref (TyArr dom rng))
             ; return(FAbs p2 body2,popFrag frag cs2)} 
    (ETuple es) -> 
      do { let (ts,xs,cs2) `acc` e = 
                   do { (t,x,cs3) <- inferFomega mess env cs2 e
                      ; return(t:ts,x:xs,cs3)}
         ; (ts,xs,cs2) <- foldM acc ([],[],cs) es
         ; p <- unifyExpect mess (TyTuple (reverse ts)) expect
         ; return(FTuple (reverse xs),cs2)} 
    ELet d e -> error ("Not yet ELet in typeFomega")
    ECase scr arms -> 
      do { (dom,scr2,cs2) <- inferFomega mess env cs scr
         ; let (arms,cs) `typArm` (pat,exp) =
                 do { (p2,frag) <- bindPat env ((dom,pat),([],[]))
                    ; (body2,cs3) <- typeFomega mess (extendPatEnv env frag) cs exp expect
                    ; return((p2,body2):arms,cs3)}
         ; (arms2,cs3) <- foldM typArm ([],cs2) arms
         ; return(FCase scr2 arms2,cs3)}
    EPolyStar (EVar nm) ->
      case lookup nm (evar env) of
       Just(t,Asterix) -> do { p <- unifyExpect mess t expect
                             ; return(FVar (nm,t),cs)}
       Just(t,Bullet) -> matchErr ((near nm ++ "Non Asterix bound term varaible: "++show nm++" used in poly."):mess)
       Nothing -> matchErr ((near nm ++ "Term varaible: "++show nm++" not in scope."):mess)                                           
    EPolyStar term -> 
      do { (typ,term2,cs2) <- inferFomega mess env cs term
         -- we want 'typ' to be an instance of 'expect'
         ; let fresh (Check t) = zonkTyp t
	       fresh (Infer ref) = do { t <- freshTyp Star; fio(writeIORef ref t); return t}
         ; expect1 <- fresh expect
         ; typ2 <- zonkTyp typ
         -- so massage 'typ' and 'expect' and then solve
         ; tree <- solve [] [(expect1,typ2,0,TRefl expect1)]
	 ; sols <- bfs [tree]
	 ; sub <- case sols of
	            [] -> matchErr ((near term++"\nIn "++show e++
	                             "\nwe can't make the type of "++show term2++
	                             "\nwhich is\n  "++show typ2++
	                             "\nan instance of the expected type\n  "++show expect1):mess)
	            (x:xs) -> return x
	 ; typ3 <- subbTyp ([],sub) typ2  -- push effects of sil into type
	 ; mapM pushSol sub               -- push effects into stateful sub
         ; (alltyp,p1,bs) <- generalizeR env typ3
	 ; term3 <- zonkFomega term2      -- make sure the effects show up in the term
         ; return(fTypAbs bs term3,cs2)}
       
    Epoly ns e pt -> 
      do { let f nm = lift1 (h nm) freshKind 
               h nm k = (nm,(TyVar (nm,k),k))
               hh (nm,(t,k)) = TypeB nm k
         ; delta <- mapM f ns
         ; let env2 = env{tvar= delta ++ (tvar env)}
         ; (pt2,kind) <- wellFormedType mess env2 pt
         ; let binds = map hh delta
         ; typeFomega mess env cs e (Check (TyAll binds pt2)) }
    EInst term (Just t) -> 
      do { (typ,kind) <- wellFormedType mess env t
         ; let notStar Star = False
               notStar x = True
         ; when (notStar kind)
                (matchErr ((near e++"\ninstan term\n  "++show e++
	 	            "\nhas type\n  "++show typ++
	 	            "\nwhich does not have kind *\n  "++show kind):mess))
         ; (term2,cs2) <- typeFomega mess env cs term (Check typ)
         ; (ts,genproof,t3) <- instanGen typ
         ; p <- unifyExpect mess t3 expect                   
	 ; term3 <- typApp term2 ts []
         ; return(term3,cs2)}        
    EInst term Nothing ->
      do { (typ,term2,cs2) <- inferFomega mess env cs term
         ; let notTyAll (TyAll _ _) = False
               notTyAll x = True
         ; when (notTyAll typ)
                (matchErr ((near e++"\ninstan* term\n  "++show e++
	 	            "\ndoes not have a polymorphic type\n  "++show typ):mess))
         ; (ts,genproof,t3) <- instanGen typ
         ; p <- unifyExpect mess t3 expect                   
	 ; term3 <- typApp term2 ts []
         ; return(term3,cs2)}         

-- Carry out explicit type-beta reduction when 
-- an abstraction is applied to a list of types
typApp (FTypAbs (b:bs) body) (t:ts) sub = typApp (FTypAbs bs body) ts (add b t sub)
  where add (TypeB nm k) t sub = (TypeS nm t k : sub)
        add _ _ sub = sub
typApp (FTypAbs bs body) ts sub = 
   do { body2 <- subbFomega (sub,[]) body
      ; return (fTypApp body2 ts) }
typApp term ts [] = return(fTypApp term ts)
         
             
         



--------------------------------------------
inferTerm :: [String] -> Env -> Constraints -> Expr -> FIO (Typ,TExpr,Constraints)
inferTerm mess env cs e = 
  do { r <- fio(newIORef (TyVar (Nm("?",noPos),Star)))
     ; (e',ds) <- typeTerm mess env cs e (Infer r)
     ; rho <- fio (readIORef r)
     ; lift1 (,e',ds) (pruneTyp rho) }
                                  
typeTerm:: [String] -> Env -> Constraints -> Expr -> Expected Typ -> FIO(TExpr,Constraints)
typeTerm mess env cs e expect = -- writeln("\nTypeExp "++show e++" : "++show expect) >>
  case e of
    ELit pos c -> 
      do { let typeOf (Left n) = intT
               typeOf (Right c) = charT
         ; p <- unifyExpect mess (typeOf c) expect
         ; return(teCast p (TELit pos c),cs) }         
    EPolyStar (EVar nm) ->
      case lookup nm (evar env) of
       Just(t,Asterix) -> do { p <- unifyExpect mess t expect
                        ; return(teCast p (TEVar (nm,t)),cs)}
       Just(t,Bullet) -> matchErr ((near nm ++ "Non Asterix bound term varaible: "++show nm++" used in poly."):mess)
       Nothing -> matchErr ((near nm ++ "Term varaible: "++show nm++" not in scope."):mess)                                        
    Epoly ns e pt -> 
      do { let f nm = lift1 (h nm) freshKind 
               h nm k = (nm,(TyVar (nm,k),k))
               hh (nm,(t,k)) = TypeB nm k
         ; delta <- mapM f ns
         ; let env2 = env{tvar= delta ++ (tvar env)}
         ; (pt2,kind) <- wellFormedType mess env2 pt
         ; let binds = map hh delta
         ; typeTerm mess env cs e (Check (TyAll binds pt2)) }
               
    EInst e pt -> error ("No EInst in typeTerm yet")
    EVar nm -> 
      case lookup nm (evar env) of
        Just (t,Asterix) ->  
           do { (_,genproof,t3) <- instanGen t
              ; p <- unifyExpect mess t3 expect
              ; return(teCast (tComp p genproof) (TEVar (nm,t)),cs)} 
        Just(t,Bullet) -> 
           do { let fresh (Check t) = return t
                    fresh (Infer ref) = do { t <- freshTyp Star; fio(writeIORef ref t); return t}
              ; alpha <- fresh expect
              ; p1 <- freshTEqual
              -- ; writeln("\n-----------\nTypeExp Var Bullet case "++show e++"\nexpect   "++show expect)
              ; cs2 <- addCon nm (alpha,p1) cs
              ; return(teCast p1 (TEVar (nm,alpha)),cs2) } 
        Nothing -> failFIOwith (loc nm) 5 "NotInScope" (show nm)
        
    (term@(EAbs p body)) ->
      case expect of
        Check (TyAll bs t) -> 
          do { -- writeln("\nTyAll case of EAbs\n  "++show expect);
               (exp2,cs2) <- typeTerm mess env cs (EAbs p body) (Check t)               
             ; p <- escapeTyAllCheck mess env bs expect e (TRefl t)
             ; return(teCast p exp2,cs2)}                                              
        Check t ->
          do { (dom,rng,p1,_) <- unifyFun mess t
             ; (p2,frag) <- bindPat env ((dom,p),([],[]))
             ; (body2,cs2) <- typeTerm mess (extendPatEnv env frag) (pushFrag frag cs) body (Check rng)
             ; let ans = (teCast (tSym p1) (TEAbs p2 body2))
             ; return(ans,popFrag frag cs2)}
        Infer ref ->
          do { dom <- freshTyp Star
             ; (p2,frag) <- bindPat env ((dom,p),([],[]))
	     ; (rng,body2,cs2) <- inferTerm mess (extendPatEnv env frag) (pushFrag frag cs) body
             ; fio(writeIORef ref (TyArr dom rng))
             ; return(TEAbs p2 body2,popFrag frag cs2)} 
    (EApp f x) ->
      do { (t,f2,cs2) <- inferTerm mess env cs f
         ; (dom,rng,p1,_) <- unifyFun (("While checking the application\n   "++ show e++"\nhas type "++show expect):mess) t
         ; (x2,cs3) <- typeTerm (("While checking the argument\n   "++show x++"\nhas type "++show dom++"\nin the application\n   "++show e):mess)
                           env cs2 x (Check dom)
         -- ; when (genVar env f && (not (mono p1)))
         --       (matchErr((near f++"Lambda bound variable used at more than one type "++show p1++"\n "++show f++" (case 2)"):mess))
         ; p2 <- unifyExpect mess rng expect         
         ; return(teCast p2 (TEApp (teCast p1 f2) x2),cs3) }
    (ETuple es) -> 
      do { let (ts,xs,cs2) `acc` e = do { (t,x,cs3) <- inferTerm mess env cs2 e; return(t:ts,x:xs,cs3)}
         ; (ts,xs,cs2) <- foldM acc ([],[],cs) es
         ; p <- unifyExpect mess (TyTuple ts) expect
         ; return(teCast p (TETuple xs),cs2)}
    ECase scr arms -> 
      do { (dom,scr2,cs2) <- inferTerm mess env cs scr
         ; let (arms,cs) `typArm` (pat,exp) =
                 do { (p2,frag) <- bindPat env ((dom,pat),([],[]))
                    ; (body2,cs3) <- typeTerm mess (extendPatEnv env frag) cs exp expect
                    ; return((p2,body2):arms,cs3)}
         ; (arms2,cs3) <- foldM typArm ([],cs2) arms
         ; return(TECase scr2 arms2,cs3)}         
             
-- Typable where all variables are kown to be Asterix

typeTermStar:: [String] -> Env -> Constraints -> Expr -> Expected Typ -> FIO(TExpr,Constraints,Bool)
typeTermStar mess env cs e expect = handleP p 6 try1 errF1
  where p x = x == "NotInScope"
        errF1 loc nm = handleP (\ _ -> True) 100 try2 errF2
        errF2 loc nm = matchErr ((near loc++" Term variable: "++nm++" not in scope."):mess)
        try1 = do { (e1,cs1) <- typeTerm mess (envStar env) cs e expect
                  ; return (e1,cs1,True)}
        try2 = do { (e1,cs1) <- typeTerm mess env cs e expect
                  ; return (e1,cs1,False)}
                  
inferTermStar :: [String] -> Env -> Constraints -> Expr -> FIO (Typ,TExpr,Constraints,Bool)
inferTermStar mess env cs e = 
  do { r <- fio(newIORef (TyVar (Nm("?",noPos),Star)))
     ; (e',ds,b) <- typeTermStar mess env cs e (Infer r)
     ; rho <- fio (readIORef r)
     ; lift1 (,e',ds,b) (pruneTyp rho) }
 




-- ===========================================================
-- Infering and computing the type of a parsed Expr, and 
-- returning a typed expression, TExpr, where all variables 
-- are tagged with their types, and all type casts are explicit

inferExp :: [String] -> Env -> Expr -> FIO (Typ, TExpr)
inferExp mess env e = 
  do { r <- fio(newIORef (TyVar (Nm("?",noPos),Star)))
     ; e' <- typeExp mess env e (Infer r)
     ; rho <- fio (readIORef r)
     ; lift1 (,e') (pruneTyp rho) }

bulletUnify env term mess t1 (Check t2) = 
   do { t3 <- pruneTyp t1
      ; t4 <- pruneTyp t2
      ; writeln("\n**************Enter Bullet Unify")
      ; case (t1,t4) of 
          (TcTv(u,ptr,k),TyAll bs body) -> 
            do { writeln("BulletUnify "++show term++": "++show t3++" generalize to? "++show t4)
               ; p <- canGeneralize env mess term t3 t4
               ; writeln("we get "++show p)
               ; return p } 
          (_,_) -> unifyExpect mess t3 (Check t4) }
bulletUnify env term mess t x = unifyExpect mess t x
    
typeExp:: [String] -> Env -> Expr -> Expected Typ -> FIO TExpr
typeExp mess env e expect = -- writeln("\nTypeExp "++show e++" : "++show expect) >>
  case e of
    ELit pos c -> 
      do { let typeOf (Left n) = intT
               typeOf (Right c) = charT
         ; p <- unifyExpect mess (typeOf c) expect
         ; return(teCast p (TELit pos c)) }
    EVar nm -> 
      case lookup nm (evar env) of
        Just (t,Asterix) ->  
           do { (_,genproof,t3) <- instanGen t
              ; p <- unifyExpect mess t3 expect
              ; return(teCast (tComp p genproof) (TEVar (nm,t)))} 
        Just(t,Bullet) -> 
           do { t2 <- zonkTyp t
              ; writeln("\n-----------\nTypeExp Var Bullet case "++show e++"\nexpect   "++show expect++"\ncomputed "++show t2++"\nno zonk "++show t)
              ; p <- unifyExpect mess t2 expect
             -- ; p <- bulletUnify env e mess t2 expect
              ; return (teCast p (TEVar (nm,t)))
             {-
             ; when (not (mono p))
                     (fail "NOT MONO")
              ; if mono p
                   then return (teCast p (TEVar (nm,t)))
                   else matchErr((near nm++"Lambda bound variable used at more than one type "++show p++" (case 1)"):mess)
             -}
             }
        Nothing -> matchErr ((near nm ++ "Term varaible: "++show nm++" not in scope."):mess)        
    EPolyStar (EVar nm) ->
      case lookup nm (evar env) of
       Just(t,_) -> do { p <- unifyExpect mess t expect
                       ; return(teCast p (TEVar (nm,t)))}
       Nothing -> matchErr ((near nm ++ "Term varaible: "++show nm++" not in scope."):mess)                               
    EPolyStar term ->
      do { (typ,term2) <- inferExp mess env term
         ; (alltyp,p1,_) <- generalizeR env typ
         -- ; writeln("In poly "++show term++"\n  "++show typ++"\n  "++show alltyp)
         ; p2 <- unifyExpect mess alltyp expect
         ; return(teCast (tComp p1 p2) term2)}
{-
    EPolyStar term (Just sigma) -> 
      do { (sigma2,kind) <- wellFormedType mess env sigma
         ; (typ,term2) <- inferExp mess env term
         ; p <- canGeneralize env mess term typ sigma2
         ; p2 <- unifyExpect mess sigma2 expect
         ; return(teCast (tComp p p2) term2) }
-}
    Epoly ns e pt -> error ("No Epoly in typeExp yet")
    EInst e pt -> error ("No EInst in typeExp yet")    
    EApp f x ->
      do { (t,f2) <- inferExp mess env f
         ; (dom,rng,p1,_) <- unifyFun (("While checking the application\n   "++ show e++"\nhas type "++show expect):mess) t
         ; x2 <- typeExp (("While checking the argument\n   "++show x++"\nhas type "++show dom++"\nin the application\n   "++show e):mess)
                         env x (Check dom)
         ; when (genVar env f && (not (mono p1)))
                (matchErr((near f++"Lambda bound variable used at more than one type "++show p1++"\n "++show f++" (case 2)"):mess))
         ; p2 <- unifyExpect mess rng expect         
         ; return(teCast p2 (TEApp (teCast p1 f2) x2)) }
    (term@(EAbs p body)) ->
      case expect of
        Check (TyAll bs t) -> 
          do { -- writeln("\nTyAll case of EAbs\n  "++show expect);
               exp2 <- typeExp mess env (EAbs p body) (Check t)               
             ; p <- escapeTyAllCheck mess env bs expect e (TRefl t)
             ; return(teCast p exp2)}                                              
        Check t ->
          do { (dom,rng,p1,_) <- unifyFun mess t
             ; (p2,frag) <- bindPat env ((dom,p),([],[]))
             ; body2 <- typeExp mess (extendPatEnv env frag) body (Check rng)
             ; let ans = (teCast (tSym p1) (TEAbs p2 body2))
             ; return ans}
        Infer ref ->
          do { dom <- freshTyp Star
             ; (p2,frag) <- bindPat env ((dom,p),([],[]))
	     ; (rng,body2) <- inferExp mess (extendPatEnv env frag) body
             ; fio(writeIORef ref (TyArr dom rng))
             ; return(TEAbs p2 body2)}
    ECase scr arms -> 
      do { (dom,scr2) <- inferExp mess env scr
         ; let typArm (pat,exp) =
                 do { (p2,frag) <- bindPat env ((dom,pat),([],[]))
                    ; body2 <- typeExp mess (extendPatEnv env frag) exp expect
                    ; return(p2,body2)}
         ; arms2 <- mapM typArm arms
         ; return(TECase scr2 arms2)}
{-
    ELet d e -> 
      do { (d2,env2) <- elab False (d,env)
         ; e2 <- typeExp mess env2 e expect
         ; return(TELet d2 e2) }
-}
    ETuple es -> error ("No ETuple in typeExp yet")         

         
canGeneralize env mess term x (TyAll vs y) =
  do { p1 <- canGeneralize env mess term x y
     ; (ptrs,names) <- tvsEnv env
     ; p2 <- escapeTyAllCheck mess env vs (TyAll vs y) term p1     
     ; return p2 }
canGeneralize env mess term (TyArr d1 r1) (TyArr d2 r2) =
  do { p1 <- unifyT mess Pos d1 d2
     ; p2 <- canGeneralize env mess term r1 r2
     ; return(tArrCong p1 p2) }
canGeneralize env mess term x y = unifyT mess Pos x y


escapeTyAllCheck mess env bs expect e p1 =
  do { (envPtrs,envNames) <- tvsEnv env
     ; case intersect (map unName envNames) (map unBind bs) of
         [] -> return (tGen bs p1)
         ts ->  matchErr (("The term\n   "++show e++"\nis not as polymorphic as expected\n   "++
                           show expect++"\nbecause the type variable(s) "++
                           plistf show "'" ts "' " "' escape.") : mess) }

zonkConst (nm,ty,pairs) = lift2 (nm,,) (zonkTyp ty) (mapM f pairs)
  where f (t,eq) = lift2 (,) (zonkTyp t) (zonkTEqual eq)

zonkConstraints name (xs,ys) = 
   do { as <- mapM zonkConst xs
      ; bs <- mapM zonkConst ys
      ; let all = (as++bs)
            input = toSolverInput all
      ; writeln("\nConstraints for "++show name++ render(ppConstraints pi0 all))

      ; tree <- solve [] input 
      ; sols <- bfs [tree]
      ; let sh [] = writeln("No solution\n")
            sh [[]] = writeln("The identity sub is a solution\n")
            sh [x] = do { writeln("\nSolution\n" ++render(pf x)++"\n")
                        ; ps <- mapM pushSol x 
                        ; return () }
            
            
            -- ff (var,TcTv p,pairs) = 
            
            pf [] = text "{}"
            pf xs = text "{" <> PP.sep(map (ppPSub pi0) xs) <> text "}"
            shTree x = do { mess <- disptree 0 0 pf x
                          ; writeln("\nTree\n"++render mess) }                        
      -- ; shTree tree
      ; sh (take 1 sols)
      ; return all
      }
 
ppConstraints p [] = PP.empty
ppConstraints p xs = PP.vcat(text "" : map f xs)
  where f (nm,t,ps) = PP.sep [ppName nm <> text ":" <+> ppTyp p t, text "{" <> ppSepBy (map g ps) ", " <> text "}" ]
        g (t,eq) = ppTyp p t -- <+> text(show eq)
        
toSolverInput zs = concat (map f zs)
  where f (nm,t,ps) = map g ps
             where g (t2,eq) = (t,t2,0,eq)

elab:: Bool -> (Decl Name Expr (Maybe(SourcePos,PTyp)),Env) -> FIO (Decl Var Fomega Typ,Env)
elab topLevel (Intro pos (Just(p1,ty)) nm e,env) =
  do { (typ,kind) <- wellFormedType [near p1++"Checking the well formedness of the type of "++show nm] env ty
     ; p2 <- unifyK [near pos++"Checking the kind of the type of "++show nm] kind Star
     ; let eplus = propExp env e (Just ty)
     ; writeln ("\n-----------------------------\nOriginal Decl term "++show nm++"\n"++show e)
     ; writeln ("\nPropogated\n"++show eplus)   
     ; (e2,cs) <- typeFomega [near pos++"Checking the type of the body of "++show nm] 
                           env ([],[]) eplus (Check typ)
     -- ; fail ("STOP WITH\n"++show eplus)   
     ; cs2 <- zonkConstraints nm cs
     ; (t2,proof,bs) <- generalizeR env typ
     ; d2 <- zonkDeclF (Intro pos t2 (nm,t2) (fTypAbs bs e2))
     ; writeln("\nFinal term\n"++show d2)
     ; qqq <- uncast (fTypAbs bs e2)
     ; writeln("\nUncasted term\n"++show qqq)
     ; return(d2,env{evar = (nm,(t2,Asterix)):(evar env)})}
elab topLevel (Intro pos Nothing nm e,env) =
  do { let eplus = propExp env e Nothing
     ; writeln ("\n-----------------------------\nOriginal Intro term "++show nm++"\n"++show e)
     ; writeln ("\nPropogated\n"++show eplus)    
     ; (typ,e2,cs) <- inferFomega [near pos++"Checking the type of the body of "++show nm]
                                env ([],[]) eplus
     ; cs2 <- zonkConstraints nm cs                           
     ; if topLevel -- only toplevel decls can be generalized without an explict poly type
          then (do { (t2,proof,bs) <- generalizeR env typ 
                   ; (full,_) <- uncast (fTypAbs bs e2)
                   ; d2 <- zonkDeclF (Intro pos t2 (nm,t2) full)
                   ; writeln("\nFinal term\n"++show d2)  
                   ; return(d2,env{evar = (nm,(t2,Asterix)):(evar env)})})
          else (do { d2 <- zonkDeclF (Intro pos typ (nm,typ) e2)
                   ; return(d2,env{evar = (nm,(typ,Bullet)):(evar env)})}) }         
elab topLevel (TypeSig pos nm t,env) = nakedTypeSig pos nm t

---------------------------------------------------------------------------------
-- Computing the type of a Pattern, this binds both term vars and type vars

extendPatEnv env (ts,es) = 
      env{evar=es++(evar env),lamBnd=(map (\ (n,(t,gp)) -> (n,t)) es)++(lamBnd env),tvar=(map f ts)++tvar env}
  where f (nm,(ty,k)) = (nm,(ty,k))                              
       
bindPat :: Env -> ((Typ,Pat Name PTyp),Frag) -> FIO(Pat Var Typ,Frag)
bindPat env ((sigma,pat),k) =  -- writeln ("\nbindpat "++show pat++": "++show sigma) >>
  let message = "\nChecking that "++show pat++" has type "++show sigma
  in case pat of
      (PVar n) -> return(PVar (n,sigma),addTermVar n sigma k)
      (PLit pos (Left n)) -> 
          do { p1 <- unifyT [message] Pos sigma intT
             ; return (PLit pos (Left n),k) }    
      (PLit pos (Right n)) -> 
          do { p1 <- unifyT [message] Pos sigma charT
             ; return (PLit pos (Right n),k) }     
      (PWild p) -> return(PWild p,k)    
      (PCon c ps) -> 
          do { (doms,rng) <- constrRho c env
             ; when (length doms < length ps) 
                    (fail (near c++"Too many arguments for constructor: "++show c++"\n   "++show pat))
             ; when (length doms > length ps) 
	            (fail (near c++"Too few arguments for constructor: "++show c++"\n   "++show pat))
             ; (ps2,frag2) <- threadM (bindPat env) (zip doms ps,k)
             ; p1 <- unifyT [message] Pos sigma rng
             ; return(PCon c ps2,frag2) }             
      (PTyp p t) -> 
          do { let mess = ["Checking well formedness of type in typed pattern: "++show pat]
                   f nm = do { k <- freshKind
                             ; t <- freshTyp k
                             ; return(nm,(t,k))}
                   g (nm,(ty,k)) = return(TypeS nm ty k)
                   h (TypeS nm t k) ans | name nm == "_" = ans
                   h (TypeS nm t k) ans = (nm,(t,k)): ans
             ; delta <- mapM f (getNamesPTyp t)
             ; (t2,kind) <- wellFormedType mess (env{tvar = delta++(tvar env)}) t
             ; sub <- mapM g delta
             ; t3 <- subbTyp (sub,[]) t2
             ; (p2,(ts,es)) <- bindPat env ((t3,p),k)
             ; proof <- unifyT [ ] Pos t3 sigma
             ; return(PTyp p2 t3,(foldr h [] sub++ts,es))}
       

constrRho c env = do { t <- find c; t2 <- instan t; unroll [] t2}
  where find c = case lookup c (evar env) of
                   Nothing -> fail (near c++"Unknown constructor: "++show c)
                   Just (typ,gp) -> pruneTyp typ
        instan (TyAll bs t) = instanPoly subbTyp (Poly bs t)
        instan t = return t
        unroll ts (TyArr t y) = unroll (t:ts) y
        unroll ts t = return(reverse ts,t)
        

threadM f ([],env) = return([],env)
threadM f (x:xs,env) = 
   do { (x2,env2) <- f (x,env); (xs2,env3) <- threadM f (xs,env2); return(x2:xs2,env3) }
       
n x = toName x

p3 = PCon (n "Cons") [PTyp (PVar (n "x")) (PTyVar (n "w")),PTyp (PVar(n "xs")) (PTyApp (PTyVar (n "ll")) (PTyVar (n "_")))]
p4 = PCon (n "Mon") [PVar (n "return"),PVar (n "bind")]
test3 p3 = do { ; writeln ("Entering test3 "++show p3)
           ; t<- freshTyp Star
           ; e <- initialEnvs >>= zonkEnv
           ; writeln ("Entering bindPat "++show p3)
           ; (p3,fr) <- bindPat e ((t,p3),([],[]))
           ; fr2 <- zonkFrag fr
           ; p4 <- zonkPat p3
           ; return(p4,fr2)}



-------------------------------------------------------------
-- Unification
-------------------------------------------------------------

-------------------------------------------------------------
-- Here are the two places that instantiation is performed 
-- 1) in function applications, and 2) in variables with Asterix tags

-- unifyFun :: [String] -> Typ -> FIO (Typ, Typ, TEqual, [Typ])
unifyFun mess x = do { x2 <- pruneTyp x; help mess x2 }
  where help mess (t@(TyArr dom rng)) = return(dom,rng,TRefl t,[])
        help mess (t@(TyAll ds body)) = 
           do { (ts,p1,body2) <- instanGen t
              ; (dom,rng,p2,ss) <- unifyFun mess body2
              ; return(dom,rng,tComp p1 p2,ts++ss)}
        help mess (t@(TcTv r)) =
           do { dom <- freshTyp Star
              ; rng <- freshTyp Star
              ; p <- unifyT mess Both t (TyArr dom rng)
              ; return(dom,rng,p,[])}
        help mess t = matchErr (("Not a function type: "++show t) : mess)

instanGen (t1@(TyAll bs t)) =
 do { sub <- freshBinder (bs,([],[]))
    ; t3 <- subbTyp sub t
    ; let f (TypeS nm t k) = t
          f (ExprS nm e t) = error ("No expr types in instanGen")
          f (KindS nm k) = error ("No kind types in instanGen")
    ; return(map f (fst sub),tSpec t (fst sub) t3,t3)}
instanGen t = return([],TRefl t,t)    

-----------------------------------------------------------------------
-- making sure we never instantiate Bullet tagged variables

genVar env (EVar nm) = case lookup nm (evar env) of { (Just(t,Bullet)) -> True; _ -> False}
genVar env _ = False

mono (TRefl _) = True
mono (TCong x y) = mono x && mono y
mono (TArrCong x y) = mono x && mono y
mono (TTupleCong xs) = foldr (\ x y -> mono x && y) True xs
mono (TVarLift x) = True
mono (TSpec _ _ _) = False
mono (TGen _ x) = mono x
mono (TComp x y) = mono x && mono y
mono (TSym x) = mono x

-------------------------------------------------------------
-- does a computed type agree with the expected type?

unifyExpect mess x (Check t) = do { p <- unifyT mess Pos x t; zonkTEqual p}
unifyExpect mess x (Infer ref) = do { fio(writeIORef ref x); zonkTEqual(TRefl x) }

unifyT:: [String] -> Variance -> Typ -> Typ -> FIO(TEqual)
unifyT mess variance x y = do { x1 <- pruneTyp x; y1 <- pruneTyp y
                   --  ; writeln("\nUnify "++show variance++" "++show x1++" =?= "++show y1)
                       ; f variance x1 y1 } where 
  f u (t1@(TyVar (n,k))) (TyVar (n1,k1)) | n==n1 =
      do { p1 <- unifyK mess k k1; return(tVarLift (n,p1))}
  f u (TyApp x y) (TyApp a b) = 
      do { c1 <- unifyT mess u x a
         ; kind <- kindOf x
         ; c2 <- case kind of
                   Karr (k1,Neg) k2 ->  unifyT mess (flipVar u) y b
                   Karr (k1,Pos) k2 ->  unifyT mess u y b
                   Karr (k1,Both) k2 -> unifyT mess Both y b
         ; return(tCong c1 c2)}
  f u (TyArr x y) (TyArr a b) = 
      do { c1 <- unifyT mess (flipVar u) x a
         ; c2 <- unifyT mess u y b
         ; return(tArrCong c1 c2)}       
  f u (t1@(TyCon n _)) (TyCon m _) | n==m = return(TRefl t1)
  f u (TyTuple xs) (TyTuple ys) 
    | length xs == length ys 
    = do { cs <- sequence(zipWith (unifyT mess variance) xs ys); return(tTupleCong cs)}
  f u (x1@(TyAll bs t)) (x2@(TyAll cs s)) =
    do { (subT,subS,ds) <- alphaSameVars mess bs cs ([],[],[])
       ; t2 <- subbTyp (subT,[]) t
       ; s2 <- subbTyp (subS,[]) s
       ; p <- unifyT mess u t2 s2
       ; (_,names1) <- getVarsTyp x1
       ; (_,names2) <- getVarsTyp x2
       ; let escape ds ns =  any (`elem` (map unName ns)) (map unBind ds) 
       ; when (escape ds (names1++names2))
              (matchErr (("Vars escape when unifying forall types\n"++show x1++" =/= "++show x2):mess))
       ; return(tGen ds p) }
  f u (t1@(TcTv (_,p1,_))) (t2@(TcTv (_,p2,_))) | p1==p2 = return(TRefl t1)
  f u (TcTv x) t2 = unifyVar mess x t2
  f u t2 (TcTv x) = do { p <- unifyVar mess x t2; return (tSym p)}
  f u x y = matchErr (diffErr x y : mess)

diffErr (x@(TyAll _ _)) y = "Different types "++show x++" =/= "++show y++"\nPerhaps you forgot a 'poly' annotation?"
diffErr x (y@(TyAll _ _)) = "Different types "++show x++" =/= "++show y++"\nPerhaps you forgot a 'poly' annotation?"
diffErr x y = "Different types "++show x++" =/= "++show y
              
freshName (Nm(n,pos)) = 
  do { m <- fio(nextInteger); return(Nm(n++show m,pos))}
  
  
              
alphaSameVars mess [] [] ans = return ans
alphaSameVars mess (TypeB n1 k1 : m1) (TypeB n2 k2 : m2) (xs,ys,bs) =
  do { unifyK mess k1 k2
     ; n3 <- freshName n1
     ; alphaSameVars mess m1 m2 
         (TypeS n1 (TyVar (n3,k1)) k1 : xs
         ,TypeS n2 (TyVar (n3,k2)) k2 : ys
         ,TypeB n3 k1: bs)}
alphaSameVars mess (KindB n1: m1) (KindB n2: m2) (xs,ys,bs) =
  do { n3 <- freshName n1
     ; alphaSameVars mess m1 m2
         (KindS n1 (Kname n3): xs
         ,KindS n2 (Kname n3): ys
         ,KindB n3: bs)}
alphaSameVars mess (ExprB n1 k1 : m1) (ExprB n2 k2 : m2) (xs,ys,bs) =
  do { unifyT mess Pos k1 k2
     ; n3 <- freshName n1
     ; alphaSameVars mess m1 m2 
         (ExprS n1 (TEVar (n3,k1)) k1 : xs
         ,ExprS n2 (TEVar (n3,k2)) k2 : ys
         ,ExprB n3 k2 : bs)}
alphaSameVars mess left right ans = 
    matchErr(("Forall type binders don't match\n  "++show (map unBind left)++"\n  "++show (map unBind right)): mess)    

-----------------------------------------------------
-- helper functions for constructing Expr
-----------------------------------------------------

applyE :: [Expr] -> Expr
applyE [t] = t
applyE [x,y] = EApp x y
applyE (f:x:xs) = applyE (EApp f x : xs)

fromBinary:: Expr -> (Expr,[Expr])
fromBinary (EApp f x) = (g,ys++[x]) where (g,ys) = fromBinary f
fromBinary f = (f,[])

fromFBinary:: Fomega -> (Fomega,[Fomega])
fromFBinary (FApp f x) = (g,ys++[x]) where (g,ys) = fromFBinary f
fromFBinary f = (f,[])

fromTBinary:: TExpr -> (TExpr,[TExpr])
fromTBinary (TEApp f x) = (g,ys++[x]) where (g,ys) = fromTBinary f
fromTBinary f = (f,[])

flatLet (ELet d e) ds = flatLet e (d:ds)
flatLet e ds = (ds,e)

flatTLet (TELet d e) ds = flatTLet e (d:ds)
flatTLet e ds = (ds,e)

flatFLet (FLet d e) ds = flatFLet e (d:ds)
flatFLet e ds = (ds,e)

applyT [] = tunit
applyT [t] = t
applyT (t:s:ts) = applyT (PTyApp t s : ts)

tunit    = PTyCon (toName "()")

------------------------------------------------------------
-- Parsing
------------------------------------------------------------
 

-- running parsers
parse1 file x s = runParser (whiteSp >> x) initState file s

parseWithName file x s =
  case parse1 file x s of
   Right(ans) -> ans
   Left message -> error (show message)
   
parse2 x s = parseWithName "keyboard input" x s   

parse3 p s = putStrLn (show state) >> return object
  where (object,state) = parse2 (do { x <- p; st <- getState; return(x,st)}) s

parseState p = (do { x <- p; (state,_) <- getState; return(x,state)})
    
parseString x s =
  case parse1 s x s of
   Right(ans) -> return ans
   Left message -> fail (show message) 

parseFile parser file =
  do {  possible <- System.IO.Error.try (readFile file)
     ; case possible of
         Right contents -> 
            case runParser (whiteSp >> parser) initState file contents of
              Right ans -> return ans
              Left message -> error(show message)
         Left err -> error(show err) }

--------------------------------------------         
-- Internal state and the type of parsers

type InternalState = ((),[Column])           -- column info for layout. This is fixed by "makeTokenParser" 
                     
initState = ((),[])
-- use (updateState,setState,getState) to access state

type MParser a = GenParser Char InternalState a

lbStyle = haskellStyle{reservedNames = 
                         ["if","then","else","case","of","let","in"
                         ,"forall", "poly", "instan"
                         ]
                      ,identStart = lower
                      }
                      
(funlog,LayFun layout) = makeTokenParser lbStyle "{" ";" "}"

----------------------------------------------------
-- lexical parsers

lexemE p    = lexeme funlog p
arrow       = lexemE(string "->")
larrow      = lexemE(string "<-")
dot         = lexemE(char '.')
under       = char '_'
parenS p    = between (symboL "(") (symboL ")") p
braceS p    = between (symboL "{") (symboL "}") p
symboL      = symbol funlog
natural10   = lexemE(number 10 digit)
whiteSp     = whiteSpace funlog
ident       = identifier funlog
sym         = symbol funlog
keyword     = reserved funlog
commA       = comma funlog
resOp       = reservedOp funlog
oper        = operator funlog
exactly s   = do { t <- ident; if s==t then return s else unexpected("Not the exact name: "++show s)}

number ::  Integer -> MParser Char -> MParser Integer
number base baseDigit
    = do{ digits <- many1 baseDigit
        ; let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
        ; seq n (return n)
        }

----------------------------------------------
-- Parsers for names

-- conName :: MParser String
conName = lexeme funlog (try construct)
  where construct = do{ c <- upper
                      ; cs <- many (identLetter lbStyle)
                      ; return(c:cs)}
                    <?> "Constructor name"
                    
nameP = do { pos <- getPosition; x <- ident; return(Nm(x,pos))}
conP = do { pos <- getPosition; x <- conName; return(Nm(x,pos))}

patvariable :: MParser (Pat Name PTyp)
patvariable = 
  do { x <- nameP
     ; let result = (PVar x)
     ; let (patname@(init:_)) = name x
     ; if isUpper init
          then fail ("pattern bindings must be lowercase, but this is not: " ++ patname)
          else return result}

expvariable  :: MParser Expr               
expvariable = do { s <- nameP; return(var s)}
  where var x = EVar x

expconstructor  :: MParser Expr
expconstructor = do { nm <- conP; return(EVar nm) }
    -- pos <- getPosition; s <- conName; return(EVar (Nm(s,pos)))}
      
kindvariable  :: MParser Kind               
kindvariable = do { s <- nameP; return(Kname s)}

tycon = do { c <- conP; return(PTyCon c)}  

typevariable = do { nm <- (wild <|> nameP)  ; return(PTyVar nm) }  
  where wild = do { p <- getPosition; s <- sym "_"; return(Nm(s,p))}

------------------------------------------------------------
-- Parsers for literals

signed p = do { f <- sign; x <- p; return(f x) }
  where sign = (char '~' >> return negate) <|>
               (return id)   
               
intLit = do{ pos <- getPosition
           ; c <- (signed natural10)
           ; return (ELit pos (Left(fromInteger c))) }
chrLit  = do{ pos <- getPosition
            ; c <- charLiteral funlog
            ; return(ELit pos (Right c)) }           
           

-------------------------------------------------
-- Parsing Patterns 

simplePattern :: MParser (Pat Name PTyp)
simplePattern =
        (do { pos <- getPosition
            ; x <- (signed natural10)
            ; return(PLit pos (Left(fromInteger x)))}) 
    <|> (do { pos <- getPosition
            ; x <- charLiteral funlog
            ; return(PLit pos (Right x))})             
    <|> (do { pos <- getPosition; sym "_"; return (PWild pos)})
    <|> try (parenS(do { p <- pattern; sym ":"; t <- typP; return(PTyp p t)}))
    <|> (do { ps <- parenS(sepBy1 pattern (sym ",")); return(makeParenP ps)})
    <|> (do { nm <- conP; return(PCon nm []) })
    <|> patvariable
    <?> "simple pattern"
    
conApp =
   (do { nm <- conP
       ; ps <- many simplePattern
       ; return(PCon nm ps)})

makeParenP [e] = e
makeParenP (x:xs) = PCon (toName "P") [x,makeParenP xs]
       
pattern :: MParser (Pat Name PTyp)
pattern = conApp <|> simplePattern <?> "pattern"   


--------------------------------------------------------------
-- Parsing Expr

simpleExpression :: MParser Expr
simpleExpression = 
        parenExpression
    <|> intLit 
    <|> chrLit
    <|> expconstructor
    <|> expvariable               -- names come last
    <?> "simple expression"

parenExpression = parenS more
  where more = do { es <- sepBy1 expr (sym ",")
                  ; return(makeParen es)}
                  
makeParen [e] = e
makeParen (x:xs) = ETuple (x:xs) -- EApp (EApp (EVar (toName "P")) x) (makeParen xs)

expr =  caseExpression
    <|> lambdaExpression
    <|> letExpression
    <|> polyExpression
    <|> instanExpression
    <|> applyExpression --names last
    <?> "expression"    

applyExpression:: MParser Expr
applyExpression =
    do{ exprs <- many1 simpleExpression
      ; return (applyE exprs)
      }  

polyExpression = do { keyword "poly"; e <- simpleExpression; oneExp e }
  where oneExp (EVar x) = oneVar x
        oneExp e = oneTyp e
        oneTyp e = return(EPolyStar e) -- do { z <- option Nothing (fmap Just typP); return(EPolyStar e z)}
        oneVar x = try (more x) <|> (oneTyp (EVar x)) 
        more x = do { xs <- many nameP
                    ; sym "."
                    ; body <- simpleExpression
                    ; sym ":"
                    ; t <- typP
                    ; return(Epoly (x:xs) body t)}
                    
instanExpression = 
  do { keyword "instan"
     ; e <- expr
     ; z <- option Nothing (do { sym ":"; t <- typP; return (Just t)})
     ;return(EInst e z) }
                    
          
          
caseExpression:: MParser Expr
caseExpression =
    do{ keyword "case"
      ; arg <- expr
      ; keyword "of"
      ; alts <- layout arm (return ())
      ; return(ECase arg alts)
      }      

arm:: MParser (Pat Name PTyp,Expr)
arm = do { pat <- pattern
         ; sym "->"
         ; e <- expr
         ; return(pat,e) }   
             
lambdaExpression :: MParser Expr
lambdaExpression =
    do{ resOp "\\"
      ; xs <- many1 simplePattern
      ; sym "->"
      ; body <- expr
      ; return(abstract xs body) } 
      
abstract [] b = b
abstract (v:vs) b = EAbs v (abstract vs b)

ignore = PTyVar (toName "_")
decl = do { pos <- getPosition; nm <- nameP; (sig pos nm) <|> (intro pos nm) }
  where intro pos nm =
          do { vs <- many simplePattern
             ; resOp "=" 
             ; body <- expr
             ; return(Intro pos Nothing nm (abstract vs body))}
        sig pos nm = 
          do { sym ":" ; t <- typP; return(TypeSig pos nm t)}

nakedTypeSig pos nm t = fail(near pos++"Type signature without body\n  "++show nm++": "++show t)

mergeDecl [] = return []
mergeDecl [TypeSig pos nm t] = nakedTypeSig pos nm t
mergeDecl(TypeSig pos nm t : TypeSig _ _ _ : _) = nakedTypeSig pos nm t
mergeDecl(TypeSig pos nm t : Intro _ _ n body : _) | nm /= n = nakedTypeSig pos nm t
mergeDecl(TypeSig p1 nm t : Intro pos _ n body : more) 
  | nm == n = do { ds <- mergeDecl more; return(Intro pos (Just(p1,t)) nm body : ds)}
mergeDecl(Intro pos t n body : more) 
  = do { ds <- mergeDecl more; return(Intro pos Nothing n body : ds)}  
        
nest [] body = body
nest (d:ds) body = ELet d (nest ds body)

letExpression = 
  do { keyword "let"
     ; ds <- layout decl (keyword "in")
     ; ds2 <- mergeDecl ds
     ; body <- expr
     ; return(nest ds2 body)}
	     
	     
program = do { ds <- layout decl (eof); mergeDecl ds }

getProgram file = parseFile program file

-----------------------------------------------------------
-- type propogation


-- varAsFunction env exp arglist
-- 1) Is "exp" an Application (EApp _ _) e.g. (f x 3 z)
-- 2) Does it have a * bound variable, f, in function position bound in "env"
-- 3) Is the variable's type compatible with the number of args in "exp"
--    e.g. (forall a b . A -> Int -> B -> C)
-- 4) Then return (f,[a,b],[(x,A),(3,Int),(z,B)],C)

varAsFunction :: Env -> Expr -> [Expr] -> Maybe (Name, [Name], [(Expr, Maybe PTyp)], PTyp)
varAsFunction env (EVar n) xs = 
  case lookup n (evar env) of
    Just(TyAll ns t,Asterix) -> 
      do { (pairs,rng) <- assocArrow t xs
         ; return(n,map unBind ns,pairs,rng) }
    Just(t @(TyArr _ _),Asterix) -> 
      do { (pairs,rng) <- assocArrow t xs
         ; return(n,[],pairs,rng) }    
    _ -> Nothing
varAsFunction env (EApp f x) xs = varAsFunction env f (x:xs)
varAsFunction env x xs = trace ("BAD EXIT " ++ show x++" "++show xs) Nothing


assocArrow:: Typ -> [Expr] -> Maybe ([(Expr,Maybe PTyp)],PTyp)
assocArrow t [] = return ([],typToPTyp t)
assocArrow (TyArr dom rng) (e:es) = 
   do { (ps,t) <- assocArrow rng es
      ; return((e,Just (typToPTyp dom)): ps,t) }
assocArrow t es = fail ("Non arrow: "++show t++" applied to args "++show es)

propDec env (Intro pos t nm e) = Intro pos t nm (propExp env e Nothing)
propDec env d = d
                 
mkPoly [] e t = e
mkPoly v e t = Epoly v e t

zzz = do { (t,k) <- wellFormedType [] env0 (parse2 typP "(forall a . a -> Int)-> Int")
         ; return(Env [] [] [(toName "h2",(t,Asterix))] [] [])}
         
-- env <- runFIO zzz (\ pos n s -> fail s)         

propExp :: Env -> Expr -> Maybe PTyp -> Expr
propExp env x t = help env x t where
  help env (EAbs p body) (Just(PTyArr dom rng)) 
   = EAbs (PTyp p dom) (propExp env body (Just rng))
--  help env (EAbs p b) (Just (PTyAll ns t)) 
--   = trace ("STOPE HERE ") (Epoly ns (propExp env (EAbs p b) (Just t)) t)
  help env anyexp (Just (PTyAll ns t)) 
   =  -- trace ("STOPE HERE ") 
     (Epoly ns (propExp env anyexp (Just t)) t)   
--  help env (EVar n) (Just (PTyAll ns t)) = Epoly ns (propExp env (EVar n) (Just t)) t
  help env (t@(EApp f x)) anytyp 
   | Just(fname,tyvars,pairs,rng) <- varAsFunction env f [x]
   = let body = applyE (EVar fname : map (uncurry (propExp env)) pairs)
         mkInst e (Just (PTyAll [] r)) = e
         mkInst e t = EInst e t         
     in mkInst (mkPoly tyvars body rng) (Just (PTyAll tyvars rng))
  help env (t@(EApp f x)) anytyp = EApp (propExp env f Nothing) (propExp env x Nothing)
  help env (ELet d e) anytyp = ELet (propDec env d) (propExp env e anytyp)
  help env (ETuple es) t = ETuple (map (\ e -> propExp env e Nothing) es)
  help env (EAbs p e) _ = EAbs p (propExp env e Nothing)
  help env (ECase e arms) t = ECase (propExp env e Nothing) (map f arms)
    where f (p,e) = (p,propExp env e t)           
  help env e t = e                           

typToPTyp :: Typ -> PTyp
typToPTyp (TyVar (n,k)) = PTyVar n
typToPTyp (TyApp x y) = PTyApp (typToPTyp x) (typToPTyp  y)
typToPTyp (TyArr x y) = PTyArr (typToPTyp x) (typToPTyp  y)
typToPTyp (TyCon n k) = PTyCon n
typToPTyp (TyTuple xs) = PTyTuple(map typToPTyp xs)
typToPTyp (TyAll bs x) = PTyAll (map unBind bs)(typToPTyp x)
typToPTyp (TcTv p) = error ("Mutable type variable in typToPTyp.")

------------------------------------------------------------
-- PTyp


simpleT = tycon <|> typevariable <|> parenS(allP <|> try tups <|> typP)

tups = do { xs <- sepBy1 typP (sym ",") ; return(PTyTuple xs)}

allP = do { keyword "forall"
          ; x <- many nameP
          ; sym "."
          ; body <- typP
          ; return(PTyAll x body)}

typP = fmap arrow (sepBy1 (fmap applyT (many1 (simpleT))) (sym "->"))
  where arrow [x] = x
        arrow (x:xs) = PTyArr x (arrow xs)
 



------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------
-- printing lists and sequences 

braces p = text "{" <> p <> text "}" 

ppSepByParen ::[Doc] -> String -> Doc
ppSepByParen xs comma = PP.parens(PP.hcat(PP.punctuate (text comma) xs))

ppSepBy:: [Doc] -> String -> Doc
ppSepBy ds x = PP.hcat (PP.punctuate (text x) ds)

ppSepByF :: (t -> Doc) -> String -> [t] -> [Doc]
ppSepByF f comma [] = []
ppSepByF f comma [x] = [f x]
ppSepByF f comma (x:xs) = ((f x)<>(text comma)):ppSepByF f comma xs


data PI = PI { printInfo :: [(String,Bool)] }

pi0 = PI []

-------------------------------------------------
-- Printing Expr

parenExpr:: PI -> Expr -> Doc
parenExpr p (x @ (EVar _)) = ppExpr p x
parenExpr p (x @ (ELit _ _)) = ppExpr p x
parenExpr p x = PP.parens $ ppExpr p x  

noParenOnApply:: PI -> Expr -> Doc
noParenOnApply p (x@(EApp _ _)) = ppExpr p x
noParenOnApply p x = parenExpr p x

ppParsedSig p nm Nothing = PP.empty
ppParsedSig p nm (Just(pos,t)) = ppName nm <> text ": " <> ppPTyp p t

ppSig p (nm,_) t = ppName nm <> text ": " <> ppTyp p t

ppExpr:: PI -> Expr -> Doc
ppExpr p e =
  case e of
    (ELit pos (Left l)) -> text(show l)
    (ELit pos (Right l)) -> text(show l)    
    (EVar (Nm(v,pos))) -> text v
    (term@(EApp _ _)) -> ppSepBy (noParenOnApply p f : (map (parenExpr p) xs)) " "
      where (f,xs) = fromBinary term
    (EAbs x ms) -> PP.sep [ text "\\" <+> ppPat pName (\ p x -> text ":" <> (ppPTyp p x)) p x, text "->"
                          , PP.nest 2 (ppExpr p ms) ]
    (e@(ELet _ _)) ->
        PP.vcat [text "let "<> ppDecl p pName ppExpr ppParsedSig d
                , PP.nest 4 (PP.vcat(map (ppDecl p pName ppExpr ppParsedSig) ds))
                ,text "in" <+> ppExpr p body]
      where (d:ds,body) = flatLet e []
    (ETuple es) -> ppSepByParen (map (ppExpr p) es) ","
    (ECase e ms) -> 
       (text "case" <+> parenExpr p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p pName (\ p x -> text ":" <> (ppPTyp p x)) ppExpr) ms)))
    (EPolyStar nm) -> PP.parens(text "poly*" <+> parenExpr p nm)
    --(EPolyStar nm (Just t)) | needsPParens t -> PP.parens(text "EPolyStar1" <+> parenExpr p nm<+> (PP.parens (ppPTyp p t)))           
    --(EPolyStar nm (Just t)) -> PP.parens(text "EPolyStar3" <+> parenExpr p nm<+> ppPTyp p t)           
    (Epoly ns e pt) -> PP.parens(PP.sep[text "poly" <+> PP.sep (map ppName ns) 
                                       ,PP.nest 3 (text ".")
                                       ,PP.nest 3 (parenExpr p e)<>text ":"
                                       ,PP.nest 3 (ppPTyp p pt)])
    
    (EInst e pt) -> PP.parens(PP.sep[text "instan",PP.nest 3 (ppExpr p e),f pt])
      where f Nothing = PP.empty
            f (Just x) = PP.nest 3 (text ":" <+> ppPTyp p x)
-----------------------------------------------
-- Decls and Match

-- ppDecl ::  PI -> (PI -> a -> Doc) -> (PI -> b -> Doc) -> Decl a b -> Doc
ppDecl p ppf ppg ppSig (Intro pos t nm exp) = 
      PP.vcat[ppSig p nm t,
      PP.sep [ppf p nm
             ,PP.nest 3 (text "=")
             ,PP.nest 3 (ppg p exp)]]        
ppDecl p ppf ppg ppt (TypeSig pos nm t) = PP.sep[ppf p nm,text ":",ppPTyp p t]             
           
ppMatch p ppN ppT ppf (pat,body) = PP.sep [ppPat ppN ppT p pat <+> text "->",PP.nest 2 (ppf p body)]

pName p v = ppName v

-----------------------------------------------------
-- FOmega

parenFomega:: PI -> Fomega -> Doc
parenFomega p (x @ (FVar _)) = ppFomega p x
parenFomega p (x @ (FLit _ _)) = ppFomega p x
parenFomega p x = PP.parens $ ppFomega p x  

noParenFomegaApply:: PI -> Fomega -> Doc
noParenFomegaApply p (x@(FApp _ _)) = ppFomega p x
noParenFomegaApply p x = parenFomega p x

ppFomega:: PI -> Fomega -> Doc
ppFomega p e = 
  case e of
    (FLit pos (Left l)) -> text(show l)
    (FLit pos (Right l)) -> text(show l)
    (FVar (nm,sch)) -> ppName nm

    (term@(FApp _ _)) -> ppSepBy (noParenFomegaApply p f : (map (parenFomega p) xs)) " "
      where (f,xs) = fromFBinary term
    (FAbs pat ms) -> 
        PP.sep [ text "\\" <+> ppPat qName2 (\ _ _ -> PP.empty) p pat
               , text "->" 
               , PP.nest 2 (ppFomega p ms) ]
    (e@(FLet _ _)) ->
        PP.vcat [text "let "<> ppDecl p qName ppFomega ppSig d
                , PP.nest 4 (PP.vcat(map (ppDecl p qName ppFomega ppSig) ds))
                ,text "in" <+> ppFomega p body]
      where (d:ds,body) = flatFLet e []                          
    (FCase e ms) -> 
       (text "case" <+> parenFomega p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p qName (\ _ _ -> PP.empty) ppFomega) ms))) 
    (FTuple es) -> ppSepByParen (map (ppFomega p) es) ","                      
    (FTypApp x ts) -> PP.sep[ppFomega p x,PP.brackets(ppSepBy (map (ppTyp p) ts) ",")]
    (FTypAbs bs x) -> PP.parens(PP.sep[text "/\\"
                                      ,PP.sep (map (ppBind p) bs)
                                      ,text "."
                                      ,ppFomega p x])
    (FCast c c2 t) -> PP.parens(PP.vcat[text "cast"
                                     ,PP.nest 3 (ppTyp p c)
                                     ,PP.nest 3 (ppTyp p c2)
                                     ,ppFomega p t])                                          
    
    
-----------------------------------------------------
-- TExpr


ppTExpr:: PI -> TExpr -> Doc
ppTExpr p e = 
  case e of
    (TELit pos (Left l)) -> text(show l)
    (TELit pos (Right l)) -> text(show l)
    (TEVar (nm,sch)) -> ppName nm

    (term@(TEApp _ _)) -> ppSepBy (noParenTExprApply p f : (map (parenTExpr p) xs)) " "
      where (f,xs) = fromTBinary term
    (TEAbs pat ms) -> 
        PP.sep [ text "\\" <+> ppPat qName2 (\ _ _ -> PP.empty) p pat
               , text "->" 
               , PP.nest 2 (ppTExpr p ms) ]
    (e@(TELet _ _)) ->
        PP.vcat [text "let "<> ppDecl p qName ppTExpr ppSig d
                , PP.nest 4 (PP.vcat(map (ppDecl p qName ppTExpr ppSig) ds))
                ,text "in" <+> ppTExpr p body]
      where (d:ds,body) = flatTLet e []       
    (TETuple es) -> ppSepByParen (map (ppTExpr p) es) ","      
    (TECase e ms) -> 
       (text "case" <+> parenTExpr p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p qName (\ _ _ -> PP.empty) ppTExpr) ms))) 
    (TECast c t) -> PP.parens(PP.vcat[text "cast"
                                     ,PP.nest 3 (ppTEqual p c)
                                     ,ppTExpr p t])               

qName2 p (nm,sch) = PP.parens(ppName nm <> text ":" <> ppTyp p sch)
qName p (nm,sch) = ppName nm  

parenTExpr:: PI -> TExpr -> Doc
parenTExpr p (x @ (TEVar _ )) = ppTExpr p x
parenTExpr p (x @ (TELit _ _)) = ppTExpr p x
parenTExpr p x = PP.parens $ ppTExpr p x 

noParenTExprApply:: PI -> TExpr -> Doc
noParenTExprApply p (x@(TEApp _ _)) = ppTExpr p x
noParenTExprApply p x = parenTExpr p x

---------------------------------------------------
-- Patterns

-- ppPat:: PI -> Pat p -> Doc
ppPat pN pT p pat =
  case pat of
    PLit p (Left l) -> text(show l)
    PLit p (Right l) -> text(show l)    
    PVar v -> pN p v
    PWild p -> text "_"
    PCon v [] -> ppName v
    PCon v ps -> PP.parens $ ppName v <+> PP.hsep (map (ppPat pN pT p) ps)
    PTyp pat t -> PP.parens(ppPat pN pT p pat <> pT p t)


-------------------------------------------------------
-- kinds

ppVariance:: PI -> (Kind,Variance) -> Doc
ppVariance p (k,Pos) = PP.parens(ppKind p k <> text ",+")
ppVariance p (k,Neg) = PP.parens(ppKind p k <> text ",-")
ppVariance p (k,Both) = PP.parens(ppKind p k <> text ",?")

ppKind:: PI -> Kind -> Doc
ppKind p Star = text "*"
-- ppKind p (Karr (x@(Karr _ _),v) y) = PP.hsep [ ppVariance(x,v), text "->", ppKind p y]       
ppKind p (Karr (x,v) y) = PP.hsep [ ppVariance p (x,v), text "->", ppKind p y]
ppKind p (Kvar (uniq,ref)) = text ("k"++show uniq)
ppKind p (Kname n) = ppName n



ppTyp :: PI -> Typ -> Doc
ppTyp p (TyVar (s,k)) = ppName s
ppTyp p (TyApp f x) | needsParens x = (ppTyp p f) <+> (PP.parens (ppTyp p x))
ppTyp p (TyApp f x) = (ppTyp p f) <+> (ppTyp p x)
ppTyp p (TyCon c k) = ppName c --  <> text"<" <> ppPolyK p k <> text">"
ppTyp p (TyTuple xs) =  ppSepByParen (map (ppTyp p) xs) "," 
ppTyp p (TyArr x y) =  PP.sep[parenTypArrow p x <+> text "->",PP.nest 1 (ppTyp p y)]
ppTyp p (TcTv (uniq,ptr,k)) = text("t"++show uniq)
ppTyp p (TyAll bs t) = PP.parens(PP.sep[text "forall"
                                           ,PP.sep (map (ppBind p) bs)
                                           ,text "."
                                           ,ppTyp p t])

                                           
ppSchema p f (Poly bs t) = PP.parens(PP.sep[text "forall"
                                           ,PP.sep (map (ppBind p) bs)
                                           ,text "."
                                           ,f p t])                                           

ppBind :: PI -> Bind -> Doc 
ppBind p (KindB nm) = ppName nm
ppBind p (TypeB nm k) = ppName nm<>text":"<>ppKind p k
ppBind p (ExprB nm t) = ppName nm<>text ":" <>ppTyp p t

parenTypArrow p (w@(TyArr x y)) = PP.parens (ppTyp p w)
parenTypArrow p w = ppTyp p w

needsParens (TyArr _ _) = True
needsParens (TyApp _ _) = True
needsParens _ = False

ppPTyp :: PI -> PTyp -> Doc
ppPTyp p (PTyVar s) = ppName s
ppPTyp p (PTyApp f x) | needsPParens x = (ppPTyp p f) <+> (PP.parens (ppPTyp p x))
ppPTyp p (PTyApp f x) = (ppPTyp p f) <+> (ppPTyp p x)
ppPTyp p (PTyCon c) = ppName c --  <> text"<" <> ppPolyK p k <> text">"
ppPTyp p (PTyTuple xs) =  ppSepByParen (map (ppPTyp p) xs) "," 
ppPTyp p (PTyArr x y) =  PP.sep[parenPTypArrow p x <+> text "->",PP.nest 1 (ppPTyp p y)]
ppPTyp p (PTyAll [] t) = ppPTyp p t
ppPTyp p (PTyAll nms t) = PP.parens(PP.sep[text "forall"
                                         ,PP.sep (map ppName nms) 
                                         ,text "."
                                         ,ppPTyp p t])

parenPTypArrow p (w@(PTyArr x y)) = PP.parens (ppPTyp p w)
parenPTypArrow p w = ppPTyp p w

needsPParens (PTyArr _ _) = True
needsPParens (PTyApp _ _) = True
needsPParens _ = False

ppPtr :: PI -> POINTER -> Doc 
ppPtr p (KindP(u,ptr)) = text("k"++show u)
ppPtr p (TypeP(u,ptr,k)) = text("t"++show u)
ppPtr p (ExprP(u,ptr,t)) = text("e"++show u) 


--data Sub  = ExprS Name TExpr Typ | TypeS Name Typ Kind | KindS Name Kind 

ppSub p (ExprS nm e t) = ppName nm <+> text "E=" <+> ppTExpr p e
ppSub p (TypeS nm t k) = ppName nm <+> text "T=" <+> ppTyp p t
ppSub p (KindS nm k)   = ppName nm <+> text "K=" <+> ppKind p k

ppPSub p (ExprPS (u,ptr,t) e) = text("e"++show u) <+> text "E=" <+> ppTExpr p e
ppPSub p (TypePS (u,ptr,k) t) = text("t"++show u) <+> text "T=" <+> ppTyp p t
ppPSub p (KindPS (u,ptr) k)   = text("k"++show u) <+> text "K=" <+> ppKind p k

------------------------------------------------
-- Show instances
------------------------------------------------

instance Show Sub where
  show x = render(ppSub pi0 x)

instance Show PSub where
  show x = render(ppPSub pi0 x)

instance Show POINTER where
   show x = render(ppPtr pi0 x)
instance Show Expr where
  show d = render(ppExpr pi0 d)
instance Show TExpr where
  show d = render(ppTExpr pi0 d)  
instance Show Fomega where
  show d = render(ppFomega pi0 d)    
instance Show (Decl Name Expr (Maybe(SourcePos,PTyp))) where
  show d = render(ppDecl pi0 pName ppExpr ppParsedSig d)
instance Show (Decl Var TExpr Typ) where
  show d = render(ppDecl pi0 qName ppTExpr ppSig d)  
instance Show (Decl Var Fomega Typ) where
  show d = render(ppDecl pi0 qName ppFomega ppSig d)    
instance Show (Pat Name PTyp) where
  show t = render(ppPat pName (\ p x -> text ":" <> ppPTyp p x) pi0 t)  
instance Show (Pat Name Typ) where
  show t = render(ppPat pName (\ p x -> text ":" <> ppTyp p x) pi0 t)  
instance Show (Pat Var Typ) where
  show t = render(ppPat qName (\ _ _ -> PP.empty) pi0 t)    
instance Show Typ where
  show d = render(ppTyp pi0 d)
instance Show PTyp where
  show d = render(ppPTyp pi0 d)
instance Show Kind where
  show d = render(ppKind pi0 d)
instance Show Variance where
  show Pos = "+"
  show Neg = "-"
  show Both = "?"
instance Show (Schema Kind) where
  show t = render(ppSchema pi0 ppKind t)

showPair (x,y) = show x++":"++show y

instance Show Env where
  show env = plistf showPair "\ntype vars = " (tvar env) "\n   " "\n" ++
             plistf showPair   "TyCons    = " (tcon env) "\n   " "\n" ++
             plistf showPair   "expr vars = " (evar env) "\n   " "\n"
  
-------------------------------------------------------
-- Location instances
-------------------------------------------------------

instance Loc SourcePos where loc x = x
instance Loc Expr where loc = expLoc
instance Loc TExpr where loc = texpLoc
instance Loc x => Loc (Pat x t) where loc = patLoc
instance Loc (Decl n e t) where loc = decLoc
instance Loc Name where
  loc (Nm(s,p)) = p
instance Loc Kind where
  loc = kindLoc
instance Loc Typ where
  loc = typLoc
instance Loc Var where
  loc (x,y) = loc x
instance Loc Bind where
  loc(ExprB n x) = loc n
  loc(TypeB n x) = loc n
  loc(KindB n) = loc n
instance Loc a => Loc [a] where
  loc [] = noPos
  loc (x:xs) = bestPos (loc x) (loc xs)

typLoc (TyVar (n,k)) = loc n
typLoc (TyApp x y) = bestPos (typLoc x) (typLoc y)
typLoc (TyArr x y) = bestPos (typLoc x) (typLoc y)
typLoc (TyCon c sch) = loc c
typLoc (TyAll bnd t) = locL (loc t) bnd
typLoc (TcTv (u,p,k)) = kindLoc k


kindLoc Star = noPos
kindLoc (Karr (k1,v) k2) = bestPos (kindLoc k1) (kindLoc k2)
kindLoc (Kvar _) = noPos
kindLoc (Kname (Nm(_,p))) = p

expLoc:: Expr -> SourcePos
expLoc (ELit p l) = p
expLoc (EVar (Nm(nm,pos))) = pos
expLoc (EApp x y) = expLoc x
expLoc (EAbs x zs) = loc x
expLoc (ELet d x) = decLoc d
expLoc (ETuple es) = loc es
expLoc (ECase x ms) = expLoc x
expLoc (EPolyStar n) = loc n
expLoc (Epoly ns e pt) = bestPos (loc ns) (loc e)
expLoc (EInst e pt) = loc e
 
patLoc (PVar nm) = loc nm
patLoc (PLit pos c) = pos
patLoc (PCon c1 ps) = loc c1
patLoc (PWild pos) = pos
patLoc (PTyp p t) = patLoc p

decLoc (Intro pos t p exp) = pos
decLoc (TypeSig pos nm t) = pos
 
texpLoc:: TExpr -> SourcePos
texpLoc (TELit p l) = p
texpLoc (TEVar (Nm(nm,pos),sch)) = pos
texpLoc (TEApp x y) = texpLoc x
texpLoc (TEAbs x zs) = loc x
texpLoc (TELet d x) = decLoc d
texpLoc (TETuple es) = loc es
texpLoc (TECase x ms) = texpLoc x
texpLoc (TECast c x) = texpLoc x

locL fpos [] = fpos
locL fpos (p:ps) = loc p


-------------------------------------------------------
-- Variables (Name) , and their associations
-------------------------------------------------------

data POINTER 
   = ExprP (Uniq, Pointer TExpr, Typ)
   | TypeP (Uniq, Pointer Typ, Kind)
   | KindP (Uniq, Pointer Kind)
   
data PSub 
   = ExprPS (Uniq, Pointer TExpr, Typ) TExpr 
   | TypePS (Uniq, Pointer Typ, Kind) Typ 
   | KindPS (Uniq, Pointer Kind) Kind
   
data Bind = ExprB Name Typ       | TypeB Name Kind     | KindB Name
data Sub  = ExprS Name TExpr Typ | TypeS Name Typ Kind | KindS Name Kind 
data NAME = ExprN Name           | TypeN Name          | KindN Name   

type Vars = ([POINTER],[NAME])

instance Eq POINTER where
  (KindP (u1,p1)) == (KindP (u2,p2)) = u1==u2
  (TypeP (u1,p1,k1)) == (TypeP (u2,p2,k2)) = u1==u2
  (ExprP (u1,p1,t1)) == (ExprP (u2,p2,t2)) = u1==u2
  _ == _ = False
  
instance Eq NAME where
  (KindN (u1)) == (KindN (u2)) = u1==u2
  (TypeN (u1)) == (TypeN (u2)) = u1==u2
  (ExprN (u1)) == (ExprN (u2)) = u1==u2
  _ == _ = False  
      
--------------------------------------------
-- transformations of one association to another

unName (ExprN n) = n
unName (TypeN n) = n
unName (KindN n) = n

unPtr (KindP (u1,p1)) = u1
unPtr (TypeP (u1,p1,k1)) = u1
unPtr (ExprP (u1,p1,t1)) = u1

unBind (ExprB n _ ) = n
unBind (TypeB n _ ) = n
unBind (KindB n) = n

unSub  (ExprS n e t) = n
unSub  (TypeS n t k) = n
unSub  (KindS n k) = n

-- Sub to Bind
subProject (ExprS nm e t) = ExprB nm t
subProject (TypeS nm t k) = TypeB nm k
subProject (KindS nm k)   = KindB nm

skolemBindToSub (ExprB nm t) =
  do { nm2 <- freshName nm; return(ExprS nm (TEVar (nm2,t)) t)}
skolemBindToSub (TypeB nm k) =
  do { nm2 <- freshName nm; return(TypeS nm (TyVar (nm2,k)) k)}
skolemBindToSub (KindB nm) =
  do { nm2 <- freshName nm; return(KindS nm (Kname nm2))}

skolem bs body = 
  do { sub <- mapM skolemBindToSub bs
     ; body2 <- subbTyp (sub,[]) body
     ; let unName (ExprS nm (TEVar (nm2,t)) _) = nm2
           unName (TypeS nm (TyVar (nm2,k)) _) = nm2
           unName (KindS nm (Kname nm2)) = nm2
     ; return(map unName sub,body2)}

-- NAME to Sub
nameToFreshSub (TypeN nm) = 
  do { k <- freshKind; t <- freshTyp k; return(TypeS nm t k)}
nameToFreshSub (KindN nm) = 
  do { k <- freshKind; return(KindS nm k)}
nameToFreshSub (ExprN nm) =
  do { t <- freshTyp Star; e <- freshExp t; return(ExprS nm e t)}

-- POINTER to (Sub,Bind)
ptrToSub:: [Name] ->    -- Names occuring in the term, these are bad so shouldn't be used.
           [POINTER] -> -- Pointers that should be generalized.
           [Name] ->    -- An infinite supply of names to choose from.
           ([Sub],[PSub]) ->     -- An initial Substitution
           FIO (([Sub],[PSub]),[Bind])    -- a substitution and a list of binders (a Telescope)
ptrToSub bad [] names env = return (env,[])  
ptrToSub bad (ps@((KindP(uniq,ptr)):more)) (n:names) (env@(ns,ptrs)) =
  if elem n bad 
     then ptrToSub bad ps names env
     else do { (env2,bs) <- ptrToSub bad more names (ns,KindPS (uniq,ptr) (Kname n): ptrs)
             ; return(env2,KindB n : bs)}
ptrToSub bad (ps@((TypeP(trip@(uniq,ptr,kind))):more)) (n:names) (env@(ns,ptrs)) =
  if elem n bad 
     then ptrToSub bad ps names env
     else  do { kind1 <- subbKind env kind
              ; (env2,bs) <- ptrToSub bad more names (ns, TypePS trip (TyVar(n,kind1)) : ptrs)
              ; return (env2,TypeB n kind1 : bs) }
ptrToSub bad (ps@((ExprP(trip@(uniq,ptr,typ))):more)) (n:names) (env@(ns,ptrs)) =
  if elem n bad 
     then ptrToSub bad ps names env
     else do { typ1 <- subbTyp env typ
             ; let term = TEVar (n,typ1)
             ; (env2,bs) <- ptrToSub bad more names (ns, ExprPS trip term: ptrs)
             ; return(env2,ExprB n typ1 : bs) }

getNamesSub :: [Sub] -> FIO [Name]
getNamesSub env = foldM getname [] env
  where ans `getname` (KindS nm k) = 
           do { (_,cl) <- getVarsKind k
              ; return(map unName cl ++ ans)}
        ans `getname` (TypeS nm t k) = 
           do { (_,cl) <- getVarsTyp t
              ; return(map unName cl ++ ans)}
        ans `getname` (ExprS nm e t) = 
           do { (_,cl) <- getVarsExpr e
              ; return(map unName cl ++ ans)}
              
ptrsOfSub :: [Sub] -> [POINTER] -> FIO [POINTER]
ptrsOfSub [] ans = return ans
ptrsOfSub((TypeS nm t2 k2):more) ans = 
  do { t3 <- pruneTyp t2
     ; case t3 of
        TcTv t -> ptrsOfSub more (TypeP t : ans)
        other -> ptrsOfSub more ans }
ptrsOfSub ((KindS nm k2):more) ans =
  do { k3 <- pruneK k2
     ; case k3 of
        Kvar t -> ptrsOfSub more (KindP t : ans)
        other -> ptrsOfSub more ans }
ptrsOfSub ((ExprS nm e2 t2):more) ans = ptrsOfSub more ans
{-
  do { e3 <- pruneE e2
     ; case e3 of
        Kvar t -> ptrsOfSub more (KindP t : ans)
        other -> ptrsOfSub more ans }  
-}        
              
                     
----------------------
-- helper functions

remove :: NAME -> [NAME] -> [Name] -> [NAME]
remove _ [] ns = []
remove x (m : more) ns =
  case (x,m) of
   (KindN _,KindN s) ->
     if elem s ns then remove x more ns else m : (remove x more ns)
   (TypeN _,TypeN s) ->
     if elem s ns then remove x more ns else m : (remove x more ns)
   (ExprN _,ExprN s) ->
     if elem s ns then remove x more ns else m : (remove x more ns)
   (_,_) -> m : (remove x more ns)

nameInfo :: NAME -> (Name, [Char], SourcePos, String)
nameInfo (KindN x) = (x,"Kind",loc x,show x)
nameInfo (TypeN x) = (x,"Type",loc x,show x)
nameInfo (ExprN x) = (x,"Exp",loc x,show x)

ptrInfo :: POINTER -> (Uniq, [Char], SourcePos, String)
ptrInfo (KindP(uniq,ptr)) = (uniq,"Kind",noPos,"k"++show uniq)
ptrInfo (TypeP(uniq,ptr,kind)) = (uniq,"Type",loc kind,"t"++show uniq)
ptrInfo (ExprP(uniq,ptr,typ)) = (uniq,"Exp",loc typ,"e"++show uniq)

compareWithErr strip x y = 
   case (strip x,strip y) of
    ((u1,tag1,pos1,nm1),(u2,tag2,pos2,nm2)) 
      | u1==u2 && tag1==tag2 -> return True
      | u1==u2 -> fail("\n*** Error ***\nThe variable: "++nm1++" is used inconsistently as a\n   "++
		       tag1++", near "++show pos1++"\nand as a\n   "++
		       tag2++", near "++show pos2++"\nPerhaps you forgot some braces { }?")
      | otherwise -> return False

unionW:: Vars -> Vars -> FIO Vars
unionW (xs,ys) (ms,ns) =  
    lift2 (,) 
          (unionByM (compareWithErr ptrInfo) xs ms) 
          (unionByM (compareWithErr nameInfo) ys ns)


showName (ExprN n) = ("expression",n)
showName (TypeN n) = ("type",n)
showName (KindN n) = ("kind",n)
showSub  (ExprS n e t) = ("expression",n)
showSub  (TypeS n t k) = ("type",n)
showSub  (KindS n k) = ("kind",n)

classFind def x [] = def
classFind def x (y:more) | unName x /= unSub y = classFind def x more
classFind def (ExprN x) ((ExprS y t w):more) = return(ExprS y t w)
classFind def (KindN x) ((KindS y t):more) = return(KindS y t)
classFind def (TypeN x) ((TypeS y t w):more) = return(TypeS y t w)
classFind def x (y:m) = fail (ycl++" variable '"++show xstr++"' used in "++xcl++" context.")
  where (xcl,xstr) = showName x
        (ycl,ystr) = showSub y

----------------------------------------------------------------
-- Important functions over Terms, Types, Kinds, and Schemas
-- prune_, zonk_, getVars_, sub_
----------------------------------------------------------------

-----------------------------------------------------
-- Schema and binders

data Schema a = Poly [Bind] a

remPair n (ptrs,names) = (ptrs,remove n names [])

getVarsPoly f (Poly [] x) = f x
getVarsPoly f (Poly (ExprB n t : more) x) = 
  do { zs <- getVarsPoly f (Poly more x)
     ; ys <- getVarsTyp t
     ; unionW ys (remPair (ExprN n) zs)}
getVarsPoly f (Poly (TypeB n k : more) x) = 
  do { zs <- getVarsPoly f (Poly more x)
     ; ys <- getVarsKind k
     ; unionW ys (remPair (TypeN n) zs)}
getVarsPoly f (Poly (KindB n : more) x) = 
  do { zs <- getVarsPoly f (Poly more x)
     ; return(remPair (ExprN n) zs)}     

zonkPoly:: (a -> FIO a) -> Schema a -> FIO (Schema a)
zonkPoly f (Poly [] x) = lift1 (Poly []) (f x)
zonkPoly f (Poly (ExprB n t : more) x) = 
  do { (Poly bs x) <- zonkPoly f (Poly more x)
     ; t2 <- zonkTyp t
     ; return(Poly ((ExprB n t2):bs) x) }
zonkPoly f (Poly (TypeB n t : more) x) = 
  do { (Poly bs x) <- zonkPoly f (Poly more x)
     ; t2 <- zonkKind t
     ; return(Poly ((TypeB n t2):bs) x) }
zonkPoly f (Poly (KindB n : more) x) = 
  do { (Poly bs x) <- zonkPoly f (Poly more x)
     ; return(Poly ((KindB n):bs) x) }     

freshNameForSub:: Name -> ([Sub],[pSub]) -> [Name] -> FIO Name
freshNameForSub name (env,_) supply = do { bad <- getNamesSub env; worker name bad supply }
  where worker name bad (n:ns) = if elem name bad then worker n bad ns else return name

-- alphaBinder:: ([Bind],[Sub]) -> FIO([Bind],[Sub])
alphaBinder ([],env) = return ([],env)
alphaBinder ((KindB nm ):xs,env) =   
  do { nm2 <- freshNameForSub nm env nameSupply  
     ; let widen (names,ptrs) = ((KindS nm (Kname nm2)):names,ptrs)
     ; (ys,env2) <- alphaBinder (xs,widen env)
     ; return((KindB nm2):ys,env2)}
alphaBinder ((TypeB nm k):xs,env) =
  do { nm2 <- freshNameForSub nm env nameSupply  
     ; k2 <- subbKind env k
     ; let widen (names,ptrs)  = ((TypeS nm (TyVar (nm2,k2)) k2):names,ptrs)
     ; (ys,env2) <- alphaBinder (xs,widen env)
     ; return((TypeB nm2 k2):ys,env2)}
alphaBinder ((ExprB nm t):xs,env) =
  do { nm2 <- freshNameForSub nm env nameSupply  
     ; t2 <- subbTyp env t
     ; let widen (names,ptrs) = ((ExprS nm (TEVar (nm2,t2)) t2):names,ptrs)
     ; (ys,env2) <- alphaBinder (xs,widen env)
     ; return((ExprB nm2 t2):ys,env2)}   


freshBinder:: ([Bind],([Sub],[PSub])) -> FIO ([Sub],[PSub])
freshBinder ([],env) = return env
freshBinder ((KindB nm ):xs,env) =   
  do { k2 <- freshKind
     ; let widen (names,ptrs) = ((KindS nm k2):names,ptrs)
     ; freshBinder (xs,widen env) }
freshBinder ((TypeB nm k):xs,env) =
  do { k2 <- subbKind env k
     ; t2 <- freshTyp k2
     ; let widen (names,ptrs)  = ((TypeS nm t2 k2):names,ptrs)
     ; freshBinder (xs,widen env) }
freshBinder ((ExprB nm t):xs,env) =
  do { t2 <- subbTyp env t
     ; e2 <- freshExp t2
     ; let widen (names,ptrs) = ((ExprS nm e2 t2):names,ptrs)
     ; freshBinder (xs,widen env)}   

        
getVarsExpr e = error("getVarsExpr not implemented yet")
freshExp t = error("freshExp not implemented yet") 
 
subPoly f env (Poly bs x) =
  do { (bs2,env2) <- alphaBinder (bs,env)
     ; x2 <- f env2 x
     ; return(Poly bs2 x2)}
     
instanPoly f (Poly bs x) =
  do { env <- freshBinder (bs,([],[]))
     ; f env x }

----------------------------------------------------    
-- Patterns

-- returns the expression level  names bound by the pattern, 
-- and the VARS appearing in the embedded Typ.

getVarsPat:: Eq n => Pat n Typ -> FIO([n],Vars)
getVarsPat (PWild pos) = return([],([],[]))
getVarsPat (PLit pos x) = return([],([],[]))
getVarsPat (PVar n) = return([n],([],[]))
getVarsPat (PTyp p t) = 
  do { (ns,vs) <- getVarsPat p
     ; us <- getVarsTyp t
     ; ws <- unionW vs us
     ; return(ns,ws)}
getVarsPat (PCon nm ps) = foldM acc ([],([],[])) ps
  where (ns,vs) `acc` p = do { (ms,us) <- getVarsPat p
                           ; ws <- unionW vs us
                           ; return(union ns ms,ws)}     
                           
                           
zonkPat:: Pat Var Typ -> FIO (Pat Var Typ)
zonkPat (PWild pos) = return(PWild pos)
zonkPat (PLit pos x) = return(PLit pos x)
zonkPat (PVar (n,t)) = lift1 (\ t -> PVar (n,t)) (zonkTyp t)
zonkPat (PTyp p t) = lift2 PTyp (zonkPat p) (zonkTyp t) 
zonkPat (PCon nm ps) = lift1 (PCon nm) (mapM zonkPat ps)

subPat:: ([Sub],[PSub]) -> Pat Var Typ -> FIO (Pat Var Typ)
subPat env (PWild pos) = return(PWild pos)
subPat env (PLit pos x) = return(PLit pos x)
subPat env (PVar (n,t)) = lift1 (\ t -> PVar (n,t)) (subbTyp env t)
subPat env (PTyp p t) = lift2 PTyp (subPat env p) (subbTyp env t) 
subPat env (PCon nm ps) = lift1 (PCon nm) (mapM (subPat env) ps)

alphaPat:: (Pat Var Typ,([Sub],[PSub])) -> FIO(Pat Var Typ,([Sub],[PSub]))
alphaPat (PWild pos,env) = return(PWild pos,env)
alphaPat (PLit pos x,env) = return(PLit pos x,env)
alphaPat (PVar (n,t),env@(names,ptrs)) = 
  do { n2 <- freshNameForSub n env nameSupply
     ; t2 <- subbTyp env t
     ; return(PVar (n2,t2),((ExprS n (TEVar (n2,t2)) t2):names,ptrs))}
alphaPat (PTyp p t,env) = 
  do { (p2,env2) <- alphaPat (p,env)
     ; t2 <- subbTyp env t
     ; return(PTyp p2 t2,env2)}
alphaPat (PCon nm ps,env) = 
  do { (ps2,env2) <- threadM alphaPat (ps,env); return(PCon nm ps2,env2)}

{-

-- Makes sure the types in embedded patterns are wellformed.
-- Not sure we need this anymore

wellFormedPat :: [String] -> Env -> (Pat Name PTyp) -> FIO (Pat Name Typ)
wellFormedPat mess env pat = 
  case pat of
    PLit pos x -> return (PLit pos x)
    PVar l -> return(PVar l)
    PWild pos -> return(PWild pos)
    PCon c ps -> lift1 (PCon c) (mapM (wellFormedPat mess env) ps)
    PTyp p t ->
      do { p2 <- wellFormedPat mess env p
         ; (t2,k) <- wellFormedType mess env t
         ; return(PTyp p2 t2)}
-}

------------------------------------------------------------- 
-- TEqual

freshTEqual = 
  do { n <- fio(nextInteger)
     ; p <- fio(newIORef Nothing)
     ; return(TVar(n,p)) }

pruneTEqual (k @ (TVar(uniq,ref))) =
  do { maybet <- fio(readIORef ref)
     ; case maybet of
         Nothing -> return k
         Just k1 -> do{k2 <- pruneTEqual k1; fio(writeIORef ref (Just k2)); return k2}}
pruneTEqual t = return t

zonkTEqual x = do { y <- pruneTEqual x; zonkEq y } where
  zonkEq (TRefl t) = lift1 TRefl (zonkTyp t) 
  zonkEq (TCong x y) = lift2 TCong (zonkTEqual x) (zonkTEqual y)
  zonkEq (TArrCong x y) = lift2 TArrCong (zonkTEqual x) (zonkTEqual y)
  zonkEq (TTupleCong xs) = lift1 TTupleCong (mapM zonkTEqual xs)
  zonkEq (TSpec t1 sub t2) = lift3 TSpec (zonkTyp t1) (mapM zonkSub sub) (zonkTyp t2)
  zonkEq (TGen b x) = lift2 TGen (mapM zonkBind b) (zonkTEqual x)
  zonkEq (TVar p) = return(TVar p)
  zonkEq (TVarLift (nm,x)) =  lift1 (\ k -> (TVarLift (nm,x))) (zonkKEq x)
  zonkEq (TComp x y) = lift2 TComp (zonkTEqual x) (zonkTEqual y)
  zonkEq (TSym x) = lift1 TSym (zonkTEqual x)


------------------------------------------------------------- 
-- Kinds

freshKind = 
  do { n <- fio(nextInteger)
     ; p <- fio(newIORef Nothing)
     ; return(Kvar(n,p)) }
     
pruneK :: Kind -> FIO Kind
pruneK (k @ (Kvar(uniq,ref))) =
  do { maybet <- fio(readIORef ref)
     ; case maybet of
         Nothing -> return k
         Just k1 -> do{k2 <- pruneK k1; fio(writeIORef ref (Just k2)); return k2}}
pruneK t = return t

zonkKind x = do { x1 <- pruneK x; f x1}
  where f (Kvar n) = return (Kvar n)
        f (Karr (x,v) y) = do { a <- zonkKind x; b <- zonkKind y; return(Karr (a,v) b) }
        f Star = return Star
        f (Kname n) = return(Kname n)
 
getVarsKind:: Kind -> FIO Vars
getVarsKind k =  do { x <- pruneK k; f x }
  where f Star = return ([],[])
        f (Karr (x,v) y) =
          do { trip1 <- getVarsKind x 
             ; trip2 <- getVarsKind y
             ; (unionW trip1 trip2)}
        f (Kvar p) = return ([KindP p],[])
        f (Kname n) = return ([],[KindN n])

matchErr:: [String] -> FIO a
matchErr xs = fail(unlines xs)

subbKind:: ([Sub],[PSub]) -> Kind -> FIO Kind
subbKind env x = do { y <- pruneK x; f y}
  where sub x = subbKind env x
        f Star = return(Star)
        f (Karr (x,v) y) = lift2 (\ k -> Karr (k,v)) (sub x) (sub y)
        f (k@(Kvar (uniq,ptr))) = return k
        f (Kname n) = do { KindS _ k <- classFind (return (KindS n (Kname n))) (KindN n) (fst env)
                         ; return k}   

----------------------------------------------------
-- Typ

freshTyp k = 
  do { n <- fio(nextInteger)
     ; p <- fio(newIORef Nothing)
     ; return(TcTv (n,p,k)) }
    
     
pruneTyp :: Typ -> FIO Typ
pruneTyp (typ @ (TcTv (uniq,ref,k))) =
  do { maybet <- fio(readIORef ref)
     ; case maybet of
         Nothing -> return typ
         Just t -> do{t2 <- pruneTyp t; fio(writeIORef ref (Just t2)); return t2}}
pruneTyp t = return t


zonkTyp :: Typ -> FIO Typ
zonkTyp t = do { x <- pruneTyp t; f x}
  where f (TyVar (s,k)) =  lift1 (\ k -> TyVar (s,k)) (zonkKind k)
        f (TyApp g x) = lift2 TyApp (zonkTyp g) (zonkTyp x)      
        f (TyArr x y) = lift2 TyArr (zonkTyp x) (zonkTyp y)              
        f (TyCon c k) = lift1 (TyCon c) (zonkKind k) -- (zonkPoly zonkKind k)
        f (TyTuple xs) = lift1 TyTuple (mapM zonkTyp xs)         
        f (TcTv (uniq,ptr,k)) =  do { k1 <- zonkKind k; return(TcTv(uniq,ptr,k1)) }
        f (TyAll bs t) =  do { (Poly bs2 ts2) <- zonkPoly zonkTyp (Poly bs t)
                             ; return(TyAll bs2 ts2)}
 
getVarsTyp:: Typ -> FIO Vars
getVarsTyp t = do { x <- pruneTyp t; f x }
  where f (TyVar (n,k)) = 
          do { pair <- getVarsKind k
             ; (unionW pair ([],[TypeN n]))}
        f (TyApp x y) =
          do { trip1 <- getVarsTyp x 
             ; trip2 <- getVarsTyp y
             ; (unionW trip1 trip2)}    
        f (TyCon c k) = getVarsKind k -- getVarsPoly getVarsKind k
        f (TyArr x y) = 
          do { trip1 <- getVarsTyp x 
             ; trip2 <- getVarsTyp y
             ; (unionW trip1 trip2)}  
        f (TyTuple ts) = foldM (\ p1 x -> do { p2 <- getVarsTyp x; unionW p1 p2}) ([],[]) ts
        f (TcTv (t@(uniq,ptr,k))) = 
          do { pair <- getVarsKind k             
             ; (unionW pair ([TypeP t],[])) }
        f (TyAll bs x) = getVarsPoly getVarsTyp (Poly bs x)         
        
getNamesPTyp:: PTyp -> [Name]
getNamesPTyp t = f t
  where f (PTyVar n) = [n]
        f (PTyApp x y) = union (getNamesPTyp x) (getNamesPTyp y)
        f (PTyCon c) = []
        f (PTyTuple xs) = foldr union [] (map getNamesPTyp xs)
        f (PTyArr x y) = union (getNamesPTyp x) (getNamesPTyp y)
        f (PTyAll bs x) = getNamesPTyp x \\ bs
          
subbTyp:: ([Sub],[PSub]) -> Typ -> FIO Typ        
subbTyp env x = do { a <- pruneTyp x; f env a }
  where f env (TyApp g x) = lift2 TyApp (subbTyp env g) (subbTyp env x)     
        f env (typ@(TyVar (s,k))) =
          do { k2 <- subbKind env k
             ; (TypeS _ t _) <- classFind (return (TypeS s (TyVar (s,k2)) k2)) (TypeN s) (fst env)
             ; return t }             
        f env (typ@(TyCon c k)) = lift1 (TyCon c) (subbKind env k) 
        f env (TyTuple xs) = lift1 TyTuple (mapM (subbTyp env) xs)
        f env (TyArr x y) = lift2 TyArr (subbTyp env x) (subbTyp env y)
        f (env@(_,ptrs)) (TcTv (uniq,ptr,k)) = find ptrs
          where find [] = lift1 (\ k -> TcTv(uniq,ptr,k)) (subbKind env k)
                find (TypePS (u,p,_) t :more) | p==ptr = return t
                find (_:more) = find more
           
        f env (TyAll bs t) = 
          do { (bs2,env2) <- alphaBinder (bs,env)
	     ; x2 <- subbTyp env2 t
	     ; return(TyAll bs2 x2)}	

subbFomega:: ([Sub],[PSub]) -> Fomega -> FIO Fomega
subbFomega sub (FLit p x) = return(FLit p x)
subbFomega sub (FVar (v,t)) = lift1 (\ x -> FVar (v,x)) (subbTyp sub t)
subbFomega sub (FApp x y) = lift2 FApp (subbFomega sub x) (subbFomega sub y)
subbFomega sub (FAbs p e) = lift2 FAbs (subPat sub p) (subbFomega sub e)
subbFomega sub (FLet d e) = lift2 FLet (subbDecl sub d) (subbFomega sub e)
subbFomega sub (FCase e xs) = lift2 FCase (subbFomega sub e) (mapM f xs)
  where f (p,e) = lift2 (,) (subPat sub p) (subbFomega sub e)
subbFomega sub (FTuple es) = lift1 FTuple (mapM (subbFomega sub) es)  
subbFomega sub (FTypApp e ts) = lift2 FTypApp (subbFomega sub e) (mapM (subbTyp sub) ts)
subbFomega sub (FTypAbs bs e) =  do { (Poly bs2 ts2) <- subPoly subbFomega sub (Poly bs e)
                                    ; return(FTypAbs bs2 ts2)}
subbFomega sub (FCast p1 p2 e) = 
   do { t1 <- (subbTyp sub p1)
      ; t2 <- (subbTyp sub p2)
      ; if t1==t2
           then (subbFomega sub e)
           else lift1 (FCast t1 t2) (subbFomega sub e)}
	     
---------------------------------------------
-- Env and operations

zonkEnv env = 
  do { tcs <- mapM (\ (n,s) -> lift1 (n,) (zonkPoly zonkKind s)) (tcon env)
     ; let f (n,(s,gp)) = do { s2 <- zonkTyp s; return(n,(s2,gp))}
     ; es <- mapM f (evar env)
     ; ts <- mapM (\ (n,(t,k)) -> let f t k = (n,(t,k))
                                  in lift2 f (zonkTyp t) (zonkKind k))
                  (tvar env)    
     ; return(env{tcon = tcs,evar = es,tvar=ts}) }


zonkFrag (ts,es) = do { ts2 <- mapM f ts; es2 <- mapM g es; return(ts2,es2)}
  where f (nm,(t,k)) = do { t2 <- zonkTyp t; k2 <- zonkKind k; return(nm,(t2,k2))}
        g (nm,(t,gp)) = do { t2 <- zonkTyp t; return(nm,(t2,gp))}  

tvsEnv :: Env -> FIO ([POINTER],[NAME])
tvsEnv env = foldM f ([],[]) monoSchemes 
  where monoSchemes = map snd (lamBnd env) 
        (ps,ns) `f` s = do { (ptrs,names) <- getVarsTyp s; return (ptrs++ps,names++ns) } 

        
generalizeR:: Env -> Typ -> FIO(Typ,TEqual, [Bind])
generalizeR env rho =
  do { (envPtrs,envNames) <- tvsEnv env
     ; (freePtrs,freeNames) <- getVarsTyp rho
     ; let genericPtrs = freePtrs \\ envPtrs   
     -- ; writeln("GenealizeR\nenv = "++show envPtrs++"\nrho = "++show freePtrs)
     ; (subst,bs) <- ptrToSub (map unName freeNames) genericPtrs nameSupply ([],[])
     ; r2 <- subbTyp subst rho
     ; zapPtrs subst
     ; r3 <- zonkTyp rho
     ; ans <- zonkTyp (tyall bs r2)
     ; return(ans,tGen bs (TRefl r3),bs)
     } 

zapPtrs(_,zs) = mapM_ f zs
  where f (ExprPS (u,ptr,t) term) = fio(writeIORef ptr (Just term))
        f (TypePS (u,ptr,k) typ) = fio(writeIORef ptr (Just typ))
        f (KindPS (u,ptr) kind) = fio(writeIORef ptr (Just kind))

tyall [] x = x
tyall bs (TyAll cs x) = TyAll (bs++cs) x     
tyall bs x = TyAll bs x


-----------------------------------------------------
zonkFomega:: Fomega -> FIO Fomega
zonkFomega (FLit p x) = return(FLit p x)
zonkFomega (FVar (v,t)) = lift1 (\ x -> FVar (v,x)) (zonkTyp t)
zonkFomega (FApp x y) = lift2 FApp (zonkFomega x) (zonkFomega y)
zonkFomega (FAbs p e) = lift2 FAbs (zonkPat p) (zonkFomega e)
zonkFomega (FLet d e) = lift2 FLet (zonkDeclF d) (zonkFomega e)
zonkFomega (FCase e xs) = lift2 FCase (zonkFomega e) (mapM f xs)
  where f (p,e) = lift2 (,) (zonkPat p) (zonkFomega e)
zonkFomega (FTuple es) = lift1 FTuple (mapM zonkFomega es)  
zonkFomega (FTypApp e ts) = lift2 FTypApp (zonkFomega e) (mapM zonkTyp ts)
zonkFomega (FTypAbs bs e) =  do { (Poly bs2 ts2) <- zonkPoly zonkFomega (Poly bs e)
                                ; return(FTypAbs bs2 ts2)}
zonkFomega (FCast p1 p2 e) = 
   do { t1 <- (zonkTyp p1)
      ; t2 <- (zonkTyp p2)
      ; if t1==t2
           then (zonkFomega e)
           else lift1 (FCast t1 t2) (zonkFomega e)}

zonkDeclF::  (Decl Var Fomega Typ) -> FIO  (Decl Var Fomega Typ)
zonkDeclF (Intro pos t (nm,s) e) = 
   lift3 (\ t s e -> Intro pos t (nm,s) e)
         (zonkTyp t) (zonkTyp s) (zonkFomega e)
zonkDeclF (TypeSig pos nm t) = return(TypeSig pos nm t)    
        
----------------------------------------------------------------------
-- TExpr

zonkExpr:: TExpr -> FIO TExpr
zonkExpr (TELit p x) = return(TELit p x)
zonkExpr (TEVar (v,t)) = lift1 (\ x -> TEVar (v,x)) (zonkTyp t)
zonkExpr (TEApp x y) = lift2 TEApp (zonkExpr x) (zonkExpr y)
zonkExpr (TEAbs p e) = lift2 TEAbs (zonkPat p) (zonkExpr e)
zonkExpr (TELet d e) = lift2 TELet (zonkDecl d) (zonkExpr e)
zonkExpr (TECase e xs) = lift2 TECase (zonkExpr e) (mapM f xs)
  where f (p,e) = lift2 (,) (zonkPat p) (zonkExpr e)
zonkExpr (TECast p e) = lift2 TECast (zonkTEqual p) (zonkExpr e)
zonkExpr (TETuple es) = lift1 TETuple (mapM zonkExpr es)

zonkDecl::  (Decl Var TExpr Typ) -> FIO  (Decl Var TExpr Typ)
zonkDecl (Intro pos t (nm,s) e) = 
   lift3 (\ t s e -> Intro pos t (nm,s) e)
         (zonkTyp t) (zonkTyp s) (zonkExpr e)
zonkDecl (TypeSig pos nm t) = return(TypeSig pos nm t)    
         
zonkKEq (KRefl k) = lift1 KRefl (zonkKind k)
zonkKEq (KArrCong (x,v) y) = lift2 (\ x y -> KArrCong(x,v) y) (zonkKEq x) (zonkKEq y)


zonkSub (ExprS nm exp typ) = lift2 (ExprS nm) (zonkExpr exp) (zonkTyp typ)
zonkSub (TypeS nm exp typ) = lift2 (TypeS nm) (zonkTyp exp) (zonkKind typ)
zonkSub (KindS nm k) = lift1 (KindS nm) (zonkKind k)
        
zonkBind (ExprB nm typ) = lift1 (ExprB nm) (zonkTyp typ)
zonkBind (TypeB nm typ) = lift1 (TypeB nm) (zonkKind typ)
zonkBind (KindB nm) = return (KindB nm)

subbTExpr sub x = error ("No subbExpr yet")
subbDecl sub x = error ("No subbDecl yet")
 

------------------------------------------------------------------
-- Unification
------------------------------------------------------------------

unifyV:: [String] -> Variance -> Variance -> FIO VarianceLift
unifyV mess Pos Pos = return (VRefl Pos)
unifyV mess Neg Neg = return (VRefl Neg)
unifyV mess Both Both = return (VRefl Both)
unifyV mess Pos Both = return PosLift
unifyV mess Neg Both = return NegLift

unifyV mess x y = return(VRefl Both)
    -- matchErr (("\nThe variance "++show x++" cannot be lifted to "++show y):mess)


unifyK :: [String] -> Kind -> Kind -> FIO KEqual
unifyK message x y = do { x1 <- pruneK x; y1 <- pruneK y; f x1 y1 }
  where f (t1@(Kvar n)) (t2@(Kvar n1)) | n==n1 = return(KRefl t1)
        f (Karr (x,v1) y) (Karr (a,v2) b) = 
            do { p1 <- unifyK message x a
               ; p2 <- unifyV message v1 v2
               ; p3 <- unifyK message y b
               ; return(kArrCong (p1,p2) p3)}
        f Star Star = return (KRefl Star)
        f (Kvar x) t = unifyVarK message x t
        f t (Kvar x) = unifyVarK message x t 
        f s t = do { s2 <- zonkKind s; t2 <- zonkKind t
                   ; matchErr (("\nDifferent kinds "++show s2++" =/= "++show t2): message)
                   }

unifyVarK message (uniq,r1) t =
  do { (vs,_) <- getVarsKind t
     ; if (any (==(KindP(uniq,r1))) vs) 
          then do { t2 <- zonkKind t
                  ; (matchErr (("\nKind occurs check "++show uniq++" in "++show vs): message))}
          else return ()
     ; fio(writeIORef r1 (Just t))
     ; return (KRefl t)
     }

flipVar Pos = Neg
flipVar Neg = Pos
flipVar Both = Both
     

unifyVar message (x@(u1,r1,k)) t =
  do { (ptrs,names) <- getVarsTyp t
     ; let same (TypeP(u0,r0,k0)) = r0==r1
           same _ = False
     ; if (any same ptrs) 
          then matchErr (("\nOccurs check "++show (TcTv x)++" occurs in "++show t): message)
          else return ()
     ; k2 <- kindOf t
     ; p <- unifyK message k k2 
     ; case p of
         KRefl _ -> return ()
         (KArrCong _ _) -> matchErr (("Different kinds in unifyVar: "++show (TcTv x)++" =?= "++show t):message)
     ; fio(writeIORef r1 (Just t))
     ; return(TRefl t)
     }
      
------------------------------------------------------------  
-- Operations on Coercion evidence
------------------------------------------------------------

-- smart constructors

kArrCong (KRefl t,VRefl v) (KRefl s)  = KRefl (Karr (t,v) s)
kArrCong x y = KArrCong x y

tCong (TRefl f) (TRefl x) = TRefl(TyApp f x)
tCong x y = TCong x y

tArrCong (TRefl f) (TRefl x) = TRefl(TyArr f x)
tArrCong x y = TArrCong x y

tTupleCong xs | Just ts <- allRefl xs = TRefl(TyTuple ts)
  where allRefl [] = return []
        allRefl (x:xs) = do { ys <- allRefl xs
                            ; case x of
                                TRefl y -> return(y:ys)
                                _ -> Nothing }
tTupleCong xs = TTupleCong xs

tComp (TRefl t) x = x
tComp x (TRefl t) = x
tComp x y = TComp x y

tVarLift (nm,KRefl k) = TRefl(TyVar (nm,k))  
tVarLift (nm,k) = TVarLift (nm,k)

tSpec t [] s = TRefl s
tSpec t bs s = TSpec t bs s

-- tGen bs (TRefl x) = TRefl (TyAll bs x)
tGen [] x = x
tGen bs x = TGen bs x

tSym (TRefl x) = TRefl x
tSym x = TSym x

teCast (TRefl t) e = e
teCast p e = TECast p e

-- visualizing what a piece of evidence justifiy as convertible

visualV (VRefl v) = (v,v)
visualV (PosLift) = (Pos,Both)
visualV (NegLift) = (Neg,Both)

visualK (KRefl k) = (k,k)
visualK (KArrCong (x,v) y) = (Karr (t,a) m, Karr (s,b) n)
  where (t,s) = visualK x
        (a,b) = visualV v
        (m,n) = visualK y

visualT (TRefl t) = (t,t)
visualT (TCong x y) = (TyApp f m,TyApp g n) 
  where (f,g) = visualT x
        (m,n) = visualT y
visualT (TArrCong x y) = (TyArr f m,TyArr g n) 
  where (f,g) = visualT x
        (m,n) = visualT y
visualT (TVarLift (nm,v)) = (TyVar (nm,a),TyVar (nm,b))
  where (a,b) = visualK v
visualT (TSpec body sub new) = (TyAll (map subProject sub) body,new)
visualT (TComp x y) = (a,d)
  where (a,b) = visualT x
        (c,d) = visualT y
visualT (TSym x) = (b,a) where (a,b) = visualT x  
visualT (TGen cs t) = (a,TyAll cs b) 
  where (a,b) = visualT t
visualT (TVar (u,p)) = (TyVar (name,Star),TyVar (name,Star))
  where name = toName ("?"++show u)
visualT (TTupleCong xs) = (TyTuple (map fst pairs),TyTuple (map snd pairs))
  where pairs = map visualT xs

ppTEqual p x = PP.vcat [ppTyp p a, PP.nest 3 (text "==>"),ppTyp p b]
  where (a,b) = visualT x
  
instance Show TEqual where
  show x = render(ppTEqual pi0 x)
 
--------------------------


main = 
  do { ds <- getProgram "tests/impred.txt"
     -- ; putStrLn(plistf show "\n" ds "\n" "\n")
     ; (tcEnv,rtEnv) <- runFIO (loadProgram ds) errF
     ; putStrLn(plistf (\(x,(t,i)) -> showPair(x,t)) "\n" (take (length ds) (evar tcEnv)) "\n" "")
     }



checkEval:: IORef (Env, t)
            -> (Env, t)
            -> Decl Name Expr (Maybe(SourcePos,PTyp))
            -> FIO (Env, t)
checkEval ref (tcEnv,rtEnv) d = 
  do { (d2,tcEnv2) <- elab True (d,tcEnv)
     -- ; writeln("\n\n"++show d2)
       --  ; rtEnv2 <- fio (evalDecC rtEnv d2 return)
     ; let ans = (tcEnv2,rtEnv)
     ; writeRef ref ans
     ; return ans }
     
checkThenEvalOneAtATime ref [] envs = return envs
checkThenEvalOneAtATime ref (d:ds) envs = 
  do { envs2 <- checkEval ref envs d
     ; checkThenEvalOneAtATime ref ds envs2 }
        


loadProgram ds = 
  do { envs <- initialEnvs
     ; ref <- newRef(envs,[])
     ; let errF loc message = do { writeln message; readRef ref }
     ; handle  5 (checkThenEvalOneAtATime ref ds (envs,[])) errF
     ; readRef ref }



errF pos n message = error (show pos ++ message)

   