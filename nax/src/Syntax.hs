{-# LANGUAGE RankNTypes, GADTs, FlexibleInstances, PatternGuards #-}

module Syntax where

-- Contains only data declarations, Eq instances and Pretty printers

import Data.IORef(newIORef,readIORef,writeIORef,IORef)

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)
import Text.Parsec.Expr(Assoc(..))

import Names
import BaseTypes
import Monads(Id,FIO,runId,lift1)
import Debug.Trace

---------------------------------------------------------
-- Pointers

type Pointer t = IORef (Maybe t)
type Uniq = Integer

---------------------------------------------------------
-- Terms


data Expr
   = ELit SourcePos Literal  -- 5, 2.3, "abc", etc.
   | EVar Name               -- x , ?x1
   | EFree Name              -- succ'       
                             -- in a type like   Sf: f {n} -> F f {succ' n}
                             -- We need to distingush that, n, is universally quantified (EVar n)
                             -- and, succ' , (EFree succ) is bound in the global environment
   | ECon Name               -- Cons, Nil
   | EApp Expr Expr          -- e1 e2                           
   | EAbs (Elim [Name]) [(Pat,Expr)]  -- (\ {i.Odd i} x -> f[x]+1)   
   | ETuple [Expr]
   | ELet (Decl Expr) Expr
   | EIn Kind Expr
   | EMend String (Elim [Typ]) Expr [([Pat],Expr)]

data TExpr 
   = TELit SourcePos Literal      -- 5, 2.3, "abc", etc.
   | TEVar Name Scheme            -- x , ?x1
   | TECon MuSyntax Name Rho Arity [TExpr]
   | TEApp (TExpr) (TExpr)        -- e1 e2                           
   | TEAbs (Elim Telescope) [(Pat,TExpr)]     -- (\ x -> f[x]+1)   
   | TETuple [TExpr]              -- (5,True,"asd")
   | TELet (Decl (TExpr)) (TExpr)
   | TEIn Kind TExpr
   | TEMend String (Elim (Telescope,[(Typ,Kind)])) (TExpr) [(Telescope,[Pat],TExpr)]
   | AppTyp (TExpr) [Typ]
   | AbsTyp Telescope TExpr
   | TECast TEqual TExpr
   | Emv (Uniq,Pointer (TExpr),Typ)  -- Typ has to be first order, I.e. data, not a function.
   | CSP (Name,Integer,Value IO)
   | ContextHole TExpr TExpr

data Pat
   = PVar Name (Maybe Typ) -- the Typ added in type-reconstruction
   | PLit SourcePos Literal
   | PTuple [Pat]
   | PCon Name [Pat]
   | PWild SourcePos

data Decl e 
   = Def SourcePos Pat e
   | DataDec SourcePos Name [Name] [(Name,[Scheme])] [Derivation]
   | GADT SourcePos Name Kind [(Name,[Name],[Scheme],Rho)] [Derivation]
   | FunDec SourcePos String [(Name,Kind)] [([Pat],e)]
   | Synonym SourcePos Name [Name] Typ -- This Typ is interpreted as a pattern

data Prog m = Prog [Decl m]

data Elim nms = ElimFun nms Typ | ElimConst

data Class k t e = Kind k | Type t | Exp e


patBinds:: Pat -> [Name] -> [Name]
patBinds (PVar n _) bound = (insert n bound)
patBinds (PLit pos _) ans = ans
patBinds (PTuple ps) ans = foldr patBinds ans ps
patBinds (PCon nm ps) ans = foldr patBinds ans ps
patBinds (PWild pos) ans = ans

------------------------------------

data Derivation =
  Syntax String

data MuSyntax = None | Syn String  deriving Show

syntax:: [Derivation] -> MuSyntax
syntax [] = None
syntax (Syntax s : xs) = Syn s
-- syntax (_ : xs) = syntax xs

------------------------------------------------------------------

data Variance = Pos | Neg | Both 

flipVar Pos = Neg
flipVar Neg = Pos
flipVar Both = Both

-------------------------------------------------------------------
-- Kinds, Types, and schemes

data Kind   
   = Star 
   | LiftK Typ             -- A first order type, Nat, Bool, but NOT (Bool -> Nat)
   | Karr Kind Kind
   | Kvar (Uniq,Pointer Kind)
   | Kname Name

data PolyKind = PolyK Telescope Kind

----------
data Term = Parsed Expr | Checked TExpr | Pattern Pat

data Typ 
   = TyVar Name Kind
   | TyApp Typ Typ
   | TyTuple Kind [Typ]  
   | TyCon MuSyntax Name PolyKind 
   | TyProof Typ Typ
   | TyArr Typ Typ
   | TySyn Name Int [Typ] Typ
   | TyMu Kind
   | TcTv (Uniq,Pointer Typ,Kind)
   | TyLift Term
   | TyAll Telescope Typ

----------
data Rho 
   = Tau Typ
   | Rarr Scheme Rho
   
data Scheme = Sch Telescope Rho

--------------
-- Type patterns

data BinTag = Arrow | Proof | Apply

data TypPat 
   = TPVar Name
   | TPCon Name
   | TPBin BinTag TypPat TypPat
   | TPTuple [TypPat]
   | TPMu Kind
   | TPLift Pat

type Tele t = [(t,Class () Kind Typ)]
type Telescope = Tele Name

whoknows = TyVar (toName "whoKnows?") Star   
------------------------------------------------------                                                                                                                                

type Arity = Int

data Value m where
   VBase :: SourcePos -> Literal -> Value m
   VFun :: Typ -> (Value m -> Value m) -> Value m
   VFunM :: Integer -> (forall a . Value m -> (Value m -> m a) -> m a) -> Value m
   VTuple :: [Value m] -> Value m
   VCon :: MuSyntax -> Arity -> String -> [Value m] -> Value m
   VIn:: Kind -> Value m -> Value m
   VInverse:: Value m -> Value m
   VCode:: TExpr -> Value m
   VProof:: Typ -> Typ -> Value m
   VType:: Typ -> Value m

--------------------------------------------------------------------
-- EQ class instances
--------------------------------------------------------------------

instance (Eq a,Eq b,Eq c) => Eq (Class a b c) where
  (Type a)==(Type b) = a==b
  (Kind a)==(Kind b) = a==b
  (Exp a)==(Exp b) = a==b
  _ == _ = False

instance Eq (Value m) where
  (VBase _ x) == (VBase _ y) = x==y
  (VTuple xs) == (VTuple ys) = xs == ys
  (VCon _ a1 i x) == (VCon _ a2 j y) = a1==a2 && i==j && x==y
  (VFunM i f) == (VFunM j g) = i==j
  (VIn _ x) == (VIn _ y) = x==y
  (VInverse x) == (VInverse y) = x==y  
  (VProof x y) == (VProof a b) = (x==a)&&(y==b)
  (VType x)== (VType y) = x==y
  (VCode x) == (VCode y) = x==y  
  _ == _ = False
 
instance Eq Pat where
  (PVar x _) == (PVar y _) = name x == name y
  (PLit _ x) == (PLit _ y) = x==y
  -- (PSum i x)== (PSum j y) = i==j && x==y
  (PTuple xs) == (PTuple ys) = xs == ys
  (PWild _) == (PWild _) = True
  (PCon c xs) == (PCon d ys) = c==d && xs == ys
  _ == _ = False
  
instance Eq Expr where
  (ELit _ x) == (ELit _ y) = x==y
  (EVar(Nm(x,_))) == (EVar(Nm(y,_))) = x==y
  (ECon n) == (ECon m) = n==m 
  (EApp x y) == (EApp a b) = x==a && y==b  
  (EAbs _ _) == (EAbs _ _) = error "No Abs in instance (Eq Expr) yet."
  (ETuple xs) == (ETuple ys) = xs == ys
  (ELet x y) == (ELet m n) = error "No Let in instance (Eq Expr) yet."
  (EIn k1 x) == (EIn k2 y) = k1==k2 && x==y
  (EMend tag1 e1 arg1 cs1) == (EMend tag2 e2 arg2 cs2) = error "No EMend in instance (Eq Expr) yet."
  _ == _ = False
  
instance Eq TExpr where
  (TELit _ x) == (TELit _ y) = x==y
  (TEVar(Nm(x,_)) sch1) == (TEVar(Nm(y,_)) sch2) = x==y
  (TECon _ n _ a1 xs) == (TECon _ m _ a2 ys) = n==m && xs==ys && a1==a2
  (TEApp x y) == (TEApp a b) = x==a && y==b  
  (TEAbs e1 ms1) == (TEAbs e2 ms2) = error "No Abs in instance (TEq Expr) yet."
  (TETuple xs) == (TETuple ys) = xs == ys
  (TELet x y) == (TELet m n) = error "No Let in instance (TEq Expr) yet."
  (TEIn k1 x) == (TEIn k2 y) = k1==k2 && x==y
  (TEMend tag1 e1 arg1 cs1) == (TEMend tag2 e2 arg2 cs2)  = error "No EMend in instance (TEq Expr) yet."
  (AppTyp x y) == (AppTyp a b) = x==a && y==b  
  (AbsTyp x y) == (AbsTyp a b) = error "No AbsTyp in instance (TEq Expr) yet."
  (TECast c1 x) == (TECast c2 y) = x==y
  (ContextHole x y ) == (ContextHole a b ) = x==a && y==b  
  (Emv (u1,_,_)) == (Emv (u2,_,_)) = u1==u2
  (CSP (nm,i,u)) == (CSP (n,j,v)) = i==j
  _ == _ = False  

instance Eq Term where
  (Parsed x)==(Parsed y) = x==y
  (Checked x)==(Checked y) = x==y
  (Pattern x) == (Pattern y) = x==y
  _ == _ = False

instance Eq Kind where
  Star == Star = True
  (LiftK s) == (LiftK t) = s==t
  (Karr x y) == (Karr a b) = x==a && y==b
  (Kvar (i,_)) == (Kvar (j,_)) = i==j
  (Kname x) == (Kname y) = x==y
  _ ==_ = False

instance Eq Typ where
  x == y = equalTyp x y

equalTyp (t1@(TyVar n k)) (t2@(TyVar n1 k1)) | n==n1 = True
equalTyp (TyApp x y) (TyApp a b) = (equalTyp x a) && (equalTyp y b)
equalTyp (TyTuple k2 xs) (TyTuple k1 ys) = all xs ys
  where all [] [] = True
        all (x:xs) (y:ys) = equalTyp x y && all xs ys
equalTyp (x@(TyCon _ s k1)) (y@(TyCon _ t k2)) = s==t 
equalTyp (TyProof x y) (TyProof m n) = x==m && y==n 
equalTyp (TyMu k1) (TyMu k2) = k1==k2
equalTyp (TcTv (u1,r1,k1)) (TcTv (u2,r2,k2)) = r1==r2
equalTyp (TyLift x) (TyLift m) = x==m    
equalTyp (TyArr x y) (TyArr a b) = equalTyp x a && equalTyp y b
equalTyp (TySyn n1 a1 xs1 b1) (TySyn n2 a2 xs2 b2) = equalTyp b1 b2
equalTyp (TyAll bs x) (TyAll cs y) = error ("No TyAll in equalTyp yet")
equalTyp s t = False

-------------------------------------------------------------
-- special syntax recognizers

toBinary f [x] = (EApp f x)
toBinary f (x:xs) = toBinary (EApp f x) xs

fromBinary:: Expr -> (Expr,[Expr])
fromBinary (EApp f x) = (g,ys++[x]) where (g,ys) = fromBinary f
fromBinary f = (f,[])

fromTBinary:: TExpr -> (TExpr,[TExpr])
fromTBinary (TEApp f x) = (g,ys++[x]) where (g,ys) = fromTBinary f
fromTBinary f = (f,[])

--- Rcognizing Char
isExprChar (ELit _ (LChar _)) = True
isExprChar _ = False

isTExprChar (TELit _ (LChar _)) = True
isTExprChar _ = False

isValueChar (VBase _ (LChar _)) = True
isValueChar _ = False

charExprOf (ELit _ (LChar c)) = c
charTExprOf (TELit _ (LChar c)) = c
charValueOf (VBase _ (LChar c)) = c  

--- recogizing Lists

isExprList (EApp (EApp (EVar (Nm("Cons",_))) x) (EIn Star y))
   = do { ys <- isExprList y; return (x:ys)}
isExprList (EVar (Nm("Nil",_))) = Just []
isExprList _ = Nothing

isTExprList -- (TEApp (TEApp (AppTyp (TEVar (Nm("C",_)) sch) [TyApp (TyMu Star) (TyApp (TyCon _ (Nm("L",_)) s) b),a]) x) (TEIn Star y)) =
            (TECon (Syn "cons") (Nm("Cons",_)) _ 2 [x,TEIn Star y]) =
   do { (a,ys) <- isTExprList y; return (a,x:ys)}
isTExprList -- (AppTyp (TEVar (Nm("N",_)) sch) [TyApp (TyMu Star) (TyApp (TyCon _ (Nm("L",_)) s) b),a]) | a==b = 
            (TECon (Syn "nil") (Nm("Nil",_)) _ 0 []) = 
   Just (0,[])
isTExprList x = Nothing -- trace ("Not a TList: "++show x) Nothing

isValueList (VIn _ (VCon _ 0 "Nil" [])) = return []
isValueList (VIn _ (VCon _ 2 "Cons" [x,xs])) =
  do { ys <- isValueList xs; return(x:ys)}
isValueList _ = Nothing  


-----------------------------------------------
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

ppConstrL c xs = PP.parens(PP.hcat (text c : xs)) 

-- (with special attention to string literals [Char])

ppList :: (Expr -> Doc) -> [Expr] -> Doc
ppList f [] = text "[]"
ppList f xs | all isExprChar xs = PP.doubleQuotes $ text (map charExprOf xs)
ppList f xs = PP.brackets(PP.fsep (ppSepByF f "," xs))  

ppTList :: (TExpr -> Doc) -> [TExpr] -> Doc
ppTList f [] = text "[]"
ppTList f xs | all isTExprChar xs = PP.doubleQuotes $ text (map charTExprOf xs)
ppTList f xs = PP.brackets(PP.fsep (ppSepByF f "," xs))  

ppVList :: (Value t -> Doc) -> [Value t] -> Doc
ppVList f [] = text "[]"
ppVList f xs | all isValueChar xs = PP.doubleQuotes $ text (map charValueOf xs)
ppVList f xs = PP.brackets(PP.fsep (ppSepByF f "," xs))  
   
-------------------------------------------------------
-- Pretty Printing
-------------------------------------------------------
--  An environment that tells how to print things
-- Passesd as the first argument to (just about) every
-- pretty printing function

data PI = PI { synonymInfo :: [Typ -> Maybe Typ]
             , pChoices :: [(String,Bool)]
             }

printChoice x p = 
 case lookup x (pChoices p) of
   Just b -> b
   Nothing -> False

pi0 = PI [] [("Mu",False),("In",False),("Cast",True),("PatType",False)] -- [listSyn,natSyn] []

listSyn (typ@(TyApp (TyMu Star) (TyApp (TyCon _ (Nm("L",_)) k) x))) = Just(TySyn (toName "List") 1 [x] typ)
listSyn _ = Nothing

natSyn (typ@(TyApp (TyMu Star)(TyCon _ (Nm("N",_)) k))) = Just(TySyn (toName "Nat") 0 [] typ)
natSyn _ = Nothing




----------------------------------------------------
-- Parenthesizing things

parenExpr:: PI -> Expr -> Doc
parenExpr p (x @ (EVar _)) = ppExpr p x
parenExpr p (x@ (EFree _)) = ppExpr p x
parenExpr p (x @ (ELit _ _)) = ppExpr p x
parenExpr p (x @ (ETuple _)) = ppExpr p x
parenExpr p (EIn Star x) | Just ys <- isExprList x  = ppList (ppExpr p) ys
parenExpr p (x @ (EIn _ _)) = ppExpr p x
parenExpr p (x @ (ECon _)) = ppExpr p x
parenExpr p x = PP.parens $ ppExpr p x  

noParenOnApply:: PI -> Expr -> Doc
noParenOnApply p (x@(EApp _ _)) = ppExpr p x
noParenOnApply p x = parenExpr p x

parensKindQ p x =
  case x of
    Star -> ppKind p x
    Kvar _ -> ppKind p x
    Kname _ -> ppKind p x
    z -> PP.parens(ppKind p z)

parenTExpr:: PI -> TExpr -> Doc
parenTExpr p (x @ (TEVar _ sch)) = ppTExpr p x
parenTExpr p (x @ (TECon _ _ _ _ _)) = ppTExpr p x
parenTExpr p (x @ (TELit _ _)) = ppTExpr p x
parenTExpr p (x @ (TETuple _)) = ppTExpr p x
parenTExpr p (x@(CSP _)) = ppTExpr p x
parenTExpr p (x@(Emv _)) = ppTExpr p x
parenTExpr p (TEIn Star x) | Just (a,ys) <- isTExprList x  = ppTList (ppTExpr p) ys
parenTExpr p (x @ (TEIn _ _)) = ppTExpr p x
parenTExpr p x = PP.parens $ ppTExpr p x 

noParenTExprApply:: PI -> TExpr -> Doc
noParenTExprApply p (x@(TEApp _ _)) = ppTExpr p x
noParenTExprApply p (x@(AppTyp _ _)) = ppTExpr p x
noParenTExprApply p x = parenTExpr p x

parenTypArrow p (w@(TyArr x y)) = PP.parens (ppTyp p w)
parenTypArrow p w = ppTyp p w

partenTExprArrow p (w@(TPBin Arrow x y)) = PP.parens (ppTypPat p w)
partenTExprArrow p w = ppTypPat p w

needsTParens (TPTuple _) = False 
needsTParens (TPBin Arrow _ _) = True
needsTParens (TPBin Apply _ _) = True
needsTParens _ = False

needsParens (TyTuple k _) = False 
needsParens (TyApp (TyCon _ (Nm("[]",_)) _) x) = False
-- needsParens (TyApp (TyApp (TyCon _ (Nm("(->)",_)) _) _) _) = True
needsParens (TyArr _ _) = True
needsParens (TyApp _ _) = True
needsParens _ = False

----------------------------------------------------------------------
-- Pretty printing Expr, and various strategies for parenthesizing

ppExpr:: PI -> Expr -> Doc
ppExpr p e =
  case e of
    (ELit pos l) -> ppLit l
    (EVar (Nm(v,pos))) -> text v
    (EFree (Nm(v,pos))) -> text("`"++v)
    (ECon (Nm(v,pos))) -> text v
    (EApp (EAbs e1 ms) e) -> 
       (text "case" <> ppElim p e1 <+> parenExpr p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppExpr) ms)))
    (term@(EApp (EApp (EVar (Nm(f,pos))) x) y))
       | infixp f -> PP.sep [(noParenOnApply p x),text f,noParenOnApply p y]
    (term@(EApp _ _)) -> ppSepBy (noParenOnApply p f : (map (parenExpr p) xs)) " "
      where (f,xs) = fromBinary term
    (EAbs elim ms) -> ((text "\\" <> ppElim p elim) $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppExpr) ms))))                 
    (ETuple ps) -> ppSepByParen (map (ppExpr p) ps) "," 
    (e@(ELet _ _)) ->
        PP.vcat [text "let "<> ppDecl p ppExpr d
                , PP.nest 4 (PP.vcat(map (ppDecl p ppExpr) ds))
                ,text "in" <+> ppExpr p body]
      where (d:ds,body) = flatLet e []
    (EIn Star x) | Just ys <- isExprList x -> ppList (ppExpr p) ys
    (EIn k x) -> PP.sep[text "(In"<>PP.brackets(parensKindQ p k),ppExpr p x]<>text ")"

    (EMend s elim exp ms) -> PP.vcat ((text s <> ppElim p elim <+> ppExpr p exp <+> text "where"): map f ms)
       where f (ps,body) = PP.nest 2(PP.sep[PP.hsep (map (ppPat p) ps) <+> text "=",PP.nest 2 (ppExpr p body)])

ppMatch p ppf (pat,body) = PP.sep [ppPat p pat <+> text "->",PP.nest 2 (ppf p body)]

flatLet (ELet d e) ds = flatLet e (d:ds)
flatLet e ds = (ds,e)
  
---------------------------------------------------------------------------------
-- TExpr

ppTExpr:: PI -> TExpr -> Doc
ppTExpr p e = 
  case e of
    (TELit pos l) -> ppLit l
    (TEVar (Nm(v,pos)) sch) -> text v
                               -- PP.parens(text v<>text":"<>ppScheme p sch)
    (TECon mu (Nm(v,pos)) typ arity []) -> text v  -- <>PP.brackets(ppRho p typ)
    (TECon mu  (Nm(v,pos)) typ arity xs) -> PP.parens(PP.sep (text v : map (parenTExpr p) xs))<>text "'"
    (TEApp (TEAbs elim ms) e) -> 
       (text "case" <> ppElim p elim <+> parenTExpr p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppTExpr) ms)))
    (term@(TEApp (TEApp (TEVar (Nm(f,pos)) sch) x) y))
       | infixp f -> PP.sep [(noParenTExprApply p x),text f,noParenTExprApply p y]

    (term@(TEApp _ _)) -> ppSepBy (noParenTExprApply p f : (map (parenTExpr p) xs)) " "
      where (f,xs) = fromTBinary term
    (TEAbs e1 ms) -> ((text "\\"<> ppElim p e1) $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppTExpr) ms))))                 
    (TETuple ps) -> ppSepByParen (map (ppTExpr p) ps) "," 
    (e@(TELet _ _)) ->
        PP.vcat [text "let "<> ppDecl p ppTExpr d
                , PP.nest 4 (PP.vcat(map (ppDecl p ppTExpr) ds))
                ,text "in" <+> ppTExpr p  body]
      where (d:ds,body) = flatLet e []
            flatLet (TELet d e) ds = flatLet e (d:ds)
	    flatLet e ds = (ds,e)
    (TEIn k x)  | printChoice "In" p -> PP.sep[text "(In"<>PP.brackets(parensKindQ p k),ppTExpr p x]<>text ")"
    (TEIn Star x) | Just (a,ys) <- isTExprList x -> ppTList (ppTExpr p) ys
    (TEIn k (TECon (Syn d) c rho 0 [])) ->  text("`"++d)
    (TEIn k (TECon (Syn d) c rho arity xs)) -> 
        PP.parens(PP.sep(text ("`"++d) : map (ppTExpr p) xs))
    
    (TEIn k x) -> PP.sep[text "(In"<>PP.brackets(parensKindQ p k),ppTExpr p x]<>text ")"
    (TEMend s elim exp ms) -> PP.vcat ((text s <> ppElim p elim <+> ppTExpr p exp <+> text "where"): map f ms)
       where f (tele,ps,body) = PP.nest 2(PP.sep[PP.brackets(PP.sep (ppKArgs p tele))
                                                ,PP.sep (map (ppPat p) ps) <+> text "="
                                                ,PP.nest 2 (ppTExpr p body)])
    (AppTyp e ts) -> ppTExpr p e <> PP.brackets(ppSepBy (map (ppTyp p) ts) ",")
    (AbsTyp vs t) -> PP.parens (PP.sep [braces(PP.sep (ppKArgs p vs)) <+> text ".", ppTExpr p t])
    (TECast c t) | printChoice "Cast" p
                 ->  PP.parens(PP.vcat[text "cast"
                                      ,PP.nest 3 (ppTEqual p c)
                                      ,ppTExpr p t]) 
    (TECast c t) -> ppTExpr p t                                      
    (ContextHole e1 e2) ->
       PP.braces(PP.vcat[ppTExpr p e1,text "=",ppTExpr p e2])
                                       
    (Emv (uniq,ptr,k)) -> text("e"++show uniq)
    (CSP (nm,i,v)) -> text("`"++show nm)
    
ppTerm p (Parsed x) = ppExpr p x -- <> text "%"
ppTerm p (Checked x) = ppTExpr p x -- <> text "#" 
ppTerm p (Pattern x) = ppPat p x    -- <> text "&" 

---------------------------------------------------
-- Patterns

ppPat:: PI -> Pat -> Doc
ppPat p pat =
  case pat of
    PLit p l -> ppLit l
    PVar v (Just t) | printChoice "PatType" p -> PP.parens(text (name v)<>text":"<>ppTyp p t)
    PVar v _ -> text (name v)
    PTuple ps -> ppSepByParen (map (ppPat p) ps) "," 
    PWild p -> text "_"
    -- PSum j p -> PP.parens(text (show j) <+> ppPat p)
    PCon (Nm(v,pos)) [] -> text v
    PCon (Nm(":",_)) (p1:ps) -> PP.parens $ ppPat p p1 <+> text  ":" <+> PP.hsep (map (ppPat p) ps)
    PCon (Nm(v,pos)) ps -> PP.parens $ text v <+> PP.hsep (map (ppPat p) ps)

----------------------------------------------------------------    
 
ppDecl ::  PI -> (PI -> a -> Doc) -> Decl a -> Doc
ppDecl p ppf (Def _ pat exp) = PP.sep [ppPat p pat
                               ,PP.nest 3 (text "=")
                               ,PP.nest 3 (ppf p exp)]
ppDecl p ppf (FunDec _ nm ts cls) = PP.vcat(map (f ts) cls)
  where f ts (ps,e) = PP.sep [text nm <+> args ts <> PP.hsep(map (ppPat p) ps) <+> text "=", PP.nest 2 (ppf p e)]
        args [] = text ""
        args ts = PP.brackets(ppSepBy (map g ts) ",") <+> (text " ")
        g (nm,k) = ppName nm
ppDecl p ppf (DataDec pos nm args cs derivs) = 
     PP.vcat
        [PP.sep[ PP.sep [text "data",ppName nm,PP.sep (map ppName args),(text "=")]
               , PP.nest 2 (ppSepBy (map f cs) " | ")]
        ,PP.sep (derivations derivs)]
  where f (c,xs) = ppName c <+> PP.sep (map ppS xs)
        g (nm,k) = PP.parens(ppName nm<>text ":"<>ppKind p k)
        ppS (Sch [] (Tau x)) =
           if needsParens x then (PP.parens (ppTyp p x)) else (ppTyp p x)
        ppS sch = PP.parens(ppScheme p sch)
ppDecl p ppf (GADT pos nm kind cs derivs) = 
     PP.vcat ((PP.sep[ text "gadt", ppName nm, text ":" , {- ppKindAll free, -} ppKind p kind, text "where"]) : 
              ((map f cs) ++ 
              (derivations derivs)))
  where g [] = text ""
        g xs = text " "<>PP.sep (map h xs) <+> text "."
        h (nm) = ppName nm
        f (constr,vs,schs,rho) = 
           PP.nest 3(PP.sep[ppName constr<> text ":" <> g vs
                           , PP.nest 3 (ppRho p (foldr Rarr rho schs))])
ppDecl p ppf (Synonym pos nm args typPat) = 
    PP.sep[text "synonym",ppName nm,ppSepBy (map ppName args) " ",text "=",ppTyp p typPat]
                           


-------------------------------------
-- Derivation

derivations [] = []      
derivations ds = (PP.nest 2 (text "deriving")):(map (\ d -> PP.nest 3(ppDerive d)) ds)

ppDerive :: Derivation -> Doc
ppDerive (Syntax s) = text("syntax "++s)


------------------------------------------------------------
-- Elim

ppElim:: Pretty a => PI -> Elim a -> Doc
ppElim p ElimConst = text ""
ppElim p (ElimFun ns t) = braces(pretty p ns <+> text "." <+> ppTyp p t)  

--------------------------------------------------------------------
-- Class

ppClass:: PI -> (PI -> a -> Doc) -> (PI -> b -> Doc) -> (PI -> c -> Doc) -> Class a b c -> Doc
ppClass p kf tf ef (Kind k) = text "K" <+> kf p k
ppClass p kf tf ef (Type t) = text "T" <+> tf p t
ppClass p kf tf ef (Exp  e) = text "E" <+> ef p e

--------------------------------------------
-- Kind

ppKind:: PI -> Kind -> Doc
ppKind p Star = text "*"
ppKind p (LiftK s) = ppTyp p s
ppKind p (Karr (x@(Karr _ _)) y) = PP.hsep [ PP.parens (ppKind p x), text "->", ppKind p y]       
ppKind p (Karr x y) = PP.hsep [ ppKind p x, text "->", ppKind p y]
ppKind p (Kvar (uniq,ref)) = text ("k"++show uniq)
ppKind p (Kname n) = ppName n

ppPolyK:: PI -> PolyKind -> Doc
ppPolyK p (PolyK [] k) = ppKind p k
ppPolyK p (PolyK zs k) = PP.sep [text "all", ppSepBy (ppKArgs p zs) "," <+> text ".", ppKind p k]

--------------------------------------------------------------------
-- Typ

isSyn p t = match (synonymInfo p) 
  where match [] = Nothing
        match (f:fs) = case f t of { Nothing -> match fs; Just w -> Just w }
        

ppTyp :: PI -> Typ -> Doc
ppTyp p t | Just w <- isSyn p t = ppTyp p w
ppTyp p (TyVar s k) = ppName s

ppTyp p (f@(TyApp _ _)) | Just (syn,ts) <- shorthand p f [] = ppTyp p (applyT (TyVar syn Star : ts))
    where applyT [t] = t
          applyT (t:s:ts) = applyT (TyApp t s : ts)

ppTyp p (TyApp (TyCon _ (Nm("[]",_)) _) x) = PP.brackets (ppTyp p x)
ppTyp p (TyApp f x) | needsParens x = (ppTyp p f) <+> (PP.parens (ppTyp p x))
ppTyp p (TyApp f x) = (ppTyp p f) <+> (ppTyp p x)
ppTyp p (TyTuple k ts) = bracket(PP.cat (PP.punctuate PP.comma (map (ppTyp p) ts)))
  where bracket = case k of { Star -> PP.parens; _ -> PP.braces}
ppTyp p (TyCon _ c k) = ppName c --  <> text"<" <> ppPolyK p k <> text">"
ppTyp p (TyMu Star) = text "Mu[*]"
ppTyp p (TyMu k) = text "Mu[" <> ppKind p k <> text "]"
ppTyp p (TcTv (uniq,ptr,k)) = text("t"++show uniq)
ppTyp p (TyLift x) = PP.braces(ppTerm p x)
ppTyp p (TyArr x y) =  PP.sep[parenTypArrow p x <+> text "->",PP.nest 1 (ppTyp p y)]
ppTyp p (TyProof x y) = PP.parens (ppTyp p x <> text "==" <> (ppTyp p y))
-- ppTyp p (TySyn n1 a1 xs1 b1) =  text "(syn " <> ppTyp p b1 <> text ")"  -- this cause infinite loop?
ppTyp p (TySyn n1 a1 xs1 b1) = PP.sep( ppName n1 : (map f xs1))
   where f x = if needsParens x then (PP.parens (ppTyp p x)) else ppTyp p x
ppTyp p (TyAll [] t) = ppTyp p t
ppTyp p (TyAll vs t) = PP.sep [PP.sep [text "forall"
                                       ,PP.nest 3 (ppSepBy (ppKArgs p vs) "," <+> text ".")]
                               ,PP.nest 3 (ppTyp p t)]



shorthand p (TyApp (TyMu k) args) ts | not(printChoice "Mu" p) = g args ts
   where g (TyCon (Syn l) c k) ts = return(toName l,ts)
         g (TyApp f t) ts = g f (t:ts)
         g _ ts = Nothing
shorthand p (TyApp f t) ts = shorthand p f (t:ts)
shorthand p x ts = Nothing

------------------------------------------------------------------------
-- Type Patterns:  TypPat

ppTypPat:: PI -> TypPat -> Doc
ppTypPat p (TPVar n) = ppName n
ppTypPat p (TPCon nm) = ppName nm
ppTypPat p (TPBin Arrow x y) = PP.sep[partenTExprArrow p x <+> text "->",PP.nest 1 (ppTypPat p y)]
ppTypPat p (TPBin Proof x y) = PP.parens (ppTypPat p x <> text "==" <> (ppTypPat p y))
ppTypPat p (TPBin Apply f x) | needsTParens x = (ppTypPat p f) <+> (PP.parens (ppTypPat p x))
ppTypPat p (TPBin Apply f x) = (ppTypPat p f) <+> (ppTypPat p x)
ppTypPat p (TPTuple ts) = PP.parens(PP.cat (PP.punctuate PP.comma (map (ppTypPat p) ts)))
ppTypPat p (TPMu k) = text "Mu[" <> ppKind p k <> text "]"
ppTypPat p (TPLift pat) = braces(ppPat p pat)


-----------------------------------------------------------
-- Rho and Scheme

ppRho:: PI -> Rho -> Doc
ppRho p (Tau x) = ppTyp p x
ppRho p (Rarr x y) = PP.sep[ppParenSch p x <+> text "->",PP.nest 1 (ppRho p y)]
 
ppScheme:: PI -> Scheme -> Doc
ppScheme p (Sch [] t) = ppRho p t
ppScheme p (Sch vs t) = PP.sep [PP.sep [text "forall"
                                       ,PP.nest 3 (ppSepBy (ppKArgs p vs) "," <+> text ".")]
                               ,PP.nest 3 (ppRho p t)]

ppKArgs p [(s,Kind ())] = [ppName s] 
ppKArgs p [(s,Type k)]  = [ppName s <> text ":" <> ppKind p k]
ppKArgs p [(s,Exp t)]   = [ppName s <> text ":" <> ppTyp p t]
ppKArgs p ((s,Kind ()):xs) = (ppName s):(ppKArgs p xs)
ppKArgs p ((s,Type k):xs)  = (ppName s <> text ":" <> ppKind p k):(ppKArgs p xs)
ppKArgs p ((s,Exp t):xs)   = (ppName s <> text ":" <> ppTyp p t):(ppKArgs p xs)
ppKArgs p [] = [PP.empty]

ppParenSch p (Sch [] (Tau t)) = parenTypArrow p t
ppParenSch p x = PP.parens (ppScheme p x)

ppKindAll [] = text ""
ppKindAll ns = text "forall" <+> ppSepBy (map ppName ns) "," <+> text "."

-----------------------------------------------------------
-- Value

ppValue:: PI -> Value m -> Doc

ppValue p (VBase _ x) = ppLit x
ppValue p (VFun ty x) = text "<Fun:" <> ppTyp p ty <> text ">"
ppValue p (VFunM n x) = text ("<FunM"++show n++">")
ppValue p (VTuple []) = text "()"
ppValue p (VTuple [x]) = error ("Value tuple with one element in ppValue")
ppValue p (VTuple xs) = 
  PP.parens(PP.fsep (ppSepByF (ppValue p) "," xs))  
ppValue p (VCon uniq arity name []) = text name
ppValue p (VCon uniq arity name xs) = 
    PP.parens(PP.fsep (text name :(ppSepByF (ppValue p) " " xs))) 
ppValue p (VIn k x) | printChoice "In" p = PP.parens(PP.sep [text "In",ppValue p x])
ppValue p (v@(VIn k _)) | Just vs <- isValueList v = ppVList (ppValue p) vs
ppValue p (VIn k (VCon (Syn d) arity c [])) = text("`"++d)
ppValue p (VIn k (VCon (Syn d) arity c vs)) = 
   PP.parens(PP.sep(text ("`"++d) : map (ppValue p) vs))
ppValue p (VIn k x) = PP.parens(PP.sep [text "In",ppValue p x])
ppValue p (VInverse x) = PP.parens(PP.sep [text "Inverse",ppValue p x])
ppValue p (VCode e) =  text "<"<> (ppTExpr p e) <> text ">"
ppValue p (VProof x y) = PP.parens(PP.sep [ppTyp p x, text "=",ppTyp p y])
ppValue p (VType t) = PP.braces(ppTyp p t)

  
 

------------------------------------------------
-- The class Pretty
-----------------------------------------------

class Pretty t where
  pretty:: PI -> t -> Doc
  
instance Pretty Name where
  pretty p n = ppName n
  
instance Pretty (Name,Kind) where
  pretty p (nm,k) = PP.parens(PP.sep[ppName nm,text ":",ppKind p k])

instance Pretty (Typ,Kind) where
  pretty p (nm,k) = PP.parens(PP.sep[ppTyp p nm,text ":",ppKind p k])  

instance Pretty n => Pretty (n, Class () Kind Typ) where 
  pretty p (s,Kind ()) = pretty p s <> text ":K" 
  pretty p (s,Type k)  = pretty p s <> text ":T " <> ppKind p k
  pretty p (s,Exp t)  =  pretty p s <> text ":E " <> ppTyp p t

instance Pretty a => Pretty [a] where
  pretty p xs = PP.fsep (ppSepByF  (pretty p) ", " xs)

instance Pretty Typ where
  pretty p x = ppTyp p x

instance Pretty (Telescope, [(Typ, Kind)]) where
  pretty p (t,xs) = pretty p t <+> text "|" <+> pretty p xs

-------------------------------------------------------
-- Show instances
-------------------------------------------------------

instance Show (Class Kind Typ TExpr) where
  show x = render(ppClass pi0 (ppKind) (ppTyp) (ppTExpr) x)
  
instance Show (Class () Kind Typ) where
  show x = render(ppClass pi0 (\ _ _ -> text "()") (ppKind) (ppTyp) x)  

instance Show (Class Name Name Name) where
  show x = render(ppClass pi0 f f f x)
    where f p x = ppName x
    
instance Show
     (Class
        (Uniq, Pointer Kind)
        (Uniq, Pointer Typ, Kind)
        (Uniq, Pointer TExpr, Typ)) where
  show x = render(ppClass pi0 f g h x)
    where f _ (u,p) = text("k"++show u)
          g _ (u,p,k) = text("t"++show u++": "++show k)
          h _ (u,p,t) = text("e"++show u++": "++show t)   

instance Show Derivation where
  show d = render(ppDerive d)
instance Show Term where
  show t = render(ppTerm pi0 t)
instance Pretty t => Show (Elim t) where
  show t = render(ppElim pi0 t)
instance Show Typ where
  show t = render(ppTyp pi0 t)
instance Show Kind where
  show t = render(ppKind pi0 t)
instance Show Scheme where
  show t = render(ppScheme pi0 t)
instance Show Rho where
  show r = render(ppRho pi0 r)
instance Show Expr where
  show d = render(ppExpr pi0 d)
instance Show TExpr where
  show d = render(ppTExpr pi0 d)  
instance Show (Decl Expr) where
  show d = render(ppDecl pi0 ppExpr d)
instance Show (Decl TExpr) where
  show d = render(ppDecl pi0 ppTExpr d)  
instance Show (Prog Expr) where
  show (Prog xs) = render(PP.vcat(map h xs))
    where h x = PP.vcat[ppDecl pi0 ppExpr x,text ""]
instance Show (Prog TExpr) where
  show (Prog xs) = render(PP.vcat(map h xs))
    where h x = PP.vcat[ppDecl pi0 ppTExpr x,text ""]    
    
instance Show Pat where
  show t = render(ppPat pi0 t)  
instance Show (Value m) where
  show t = render(ppValue pi0 t) 
instance Show Literal where
  show l = render(ppLit l)
  
instance Show PolyKind where
  show p = render(ppPolyK pi0 p)
instance Show TypPat where
  show p = render(ppTypPat pi0 p)


showPair (x,y) = show x++":"++show y

----------------------------------------------------------------------
-- for debugging when you need to see all the structure of a type

showK Star = "Star"
showK (Karr x y) = "(Karr "++showK x++" "++showK y++")"
showK (Kname s) = "(Kname "++show s++")"
showK (Kvar (uniq,ptr)) = "k"++show uniq
showK (LiftK t) = "(LiftK "++showT t++")"

showT (TyVar s k) = "(TyVar "++show s++" "++show k++")"
showT (TyCon (Syn m) s k) = "(Con "++show s++" "++show k++" muSyn="++ m++")"
showT (TyCon None s k) = "(Con "++show s++" "++show k ++ ")"
showT (TyTuple Star xs) = plistf showT "(Tuple* " xs "," ")"
showT (TyTuple _ xs) = plistf showT "(Tuple# " xs "," ")"
showT (TcTv (uniq,ptr,k)) = "(Tv "++show uniq++" "++show k++")"
showT (TyApp f x) = "("++showT f++ " "++showT x++")"
showT (TyProof s x) = "(TyProof "++showT s++ " "++showT x++")"
showT (TyArr s x) = "(TyArr "++showT s++ " -> "++showT x++")"
showT (TySyn nm arity xs body) = "(TYSyn "++show nm++" "++show arity++
                                 plistf showT " [" xs "," "]="++showT body ++")"
showT (TyMu k) = "Mu "++show k
showT (TyLift x) = "{"++show x++"}"
showT (TyAll vs r) = "(TyAll ... "++show r++")"


showR (Tau t) = "(Tau "++showT t++")"
showR (Rarr s x) = "(Rarr "++showS s++ " "++showR x++")"


showS (Sch vs r) = "(Sch ... "++showR r++")"
  

------------------------------------------------------------------
-- Defining Infix and Prefix operators
-- Create a datastructure parameterized by two functions
-- Use (1) obtain a list of all operators
--     (2) Create a structure for input to buildExpressionParser
------------------------------------------------------------------

opList prefix infiX =
    [ [ prefix "~" ]            -- negation
    , [ infiX "!!" AssocLeft]
    , [ infiX "^"  AssocRight]  -- exponentiation
    , [ infiX "*"  AssocLeft, infiX "/"  AssocLeft]
    , [ infiX "+"  AssocLeft, infiX "-"  AssocLeft]
    , [ infiX ":" AssocRight]
    , [ infiX "++" AssocRight]
    , [ infiX "==" AssocNone, infiX "/=" AssocNone, infiX "<"  AssocNone
      , infiX "<=" AssocNone, infiX ">"  AssocNone, infiX ">=" AssocNone ]
    , [ infiX "&&" AssocRight ]  -- Boolean and
    , [ infiX "||" AssocRight, infiX "=>" AssocRight ] -- boolean Or and implication
    , [ infiX "$" AssocRight ]  -- right assoc application
    , [ infiX "." AssocLeft]    -- composition
   ]

-- Use (1)

mendlerOps = filter (/="") (concat (opList prefix op))
  where prefix x = ""
        op x y = x  
        
infixp s = elem s mendlerOps      

-----------------------------------------------------------
-- A few useful functions

mapMDecl :: Monad m => (t -> m a) -> (Pat -> m Pat) -> Decl t -> m (Decl a)
mapMDecl f g (Def loc p e) = do { e2 <- f e; p2 <- g p; return(Def loc p2 e2)}
mapMDecl f g (DataDec loc nm args cs derivs) = return(DataDec loc nm args cs derivs)
mapMDecl f g (GADT loc nm kind cs derivs) = return(GADT loc nm kind cs derivs)
mapMDecl f h (FunDec pos nm ts cls) = lift1 (FunDec pos nm ts) (mapM g cls)
  where g (ps,e) = do { e2 <- f e; ps2 <- mapM h ps; return(ps2,e2)}
mapMDecl f g (Synonym pos nm xs typ) = return(Synonym pos nm xs typ)

mapDecl f x = runId (mapMDecl (return . f) return x)
      

toPat:: Typ -> TypPat
toPat (TyVar n k) = TPVar n
toPat (TyApp x y) = TPBin Apply (toPat x) (toPat y)
toPat (TyTuple _ xs) = TPTuple (map toPat xs)
toPat (TyCon _ n _) = TPCon n
toPat (TyProof x y) = TPBin Proof (toPat x) (toPat y)
toPat (TyArr x y) = TPBin Arrow (toPat x) (toPat y)
toPat (TySyn nm i xs t) = toPat t
toPat (TyMu k) = TPMu k
toPat (TyLift(Pattern p)) = TPLift p
toPat (TyAll bs v) = error ("No TyAll in toPat yet")
toPat (TyLift x) = error ("Non pattern in TyLift in Type Pattern context: "++show x)

 
----------------------------------------------
-- locations 
----------------------------------------------


instance Loc Expr where loc = expLoc
instance Loc TExpr where loc = texpLoc
instance Loc Pat where loc = patLoc
instance Loc (Decl t) where loc = decLoc
instance Loc Name where
  loc (Nm(s,p)) = p
instance Loc Kind where
  loc = kindLoc
instance Loc Typ where
  loc = typLoc
instance Loc (Elim [Name]) where
  loc = elimLoc  
  

typLoc (TyVar n k) = loc n
typLoc (TyApp x y) = bestPos (typLoc x) (typLoc y)
typLoc (TyTuple k xs) = foldr bestPos noPos (map typLoc xs)
typLoc (TyCon _ (Nm(_,p)) _) = p
typLoc (TyProof x y) = bestPos (typLoc x) (typLoc y)
typLoc (TyMu k) = kindLoc k
typLoc (TcTv (u,p,k)) = kindLoc k
typLoc (TyLift (Parsed x)) = loc x
typLoc (TyLift (Checked x)) = loc x
typLoc (TyLift (Pattern x)) = loc x
typLoc (TyArr x y) = bestPos (typLoc x) (typLoc y)
typLoc (TySyn n1 a1 xs1 b1) = loc n1
typLoc (TyAll bs t) = loc t


kindLoc Star = noPos
kindLoc (LiftK t) = typLoc t
kindLoc (Karr k1 k2) = bestPos (kindLoc k1) (kindLoc k2)
kindLoc (Kvar _) = noPos
kindLoc (Kname (Nm(_,p))) = p

expLoc:: Expr -> SourcePos
expLoc (ELit p l) = p
expLoc (EVar (Nm(nm,pos))) = pos
expLoc (EFree (Nm(n,pos))) = pos
expLoc (ECon (Nm(nm,pos))) = pos
expLoc (EApp x y) = expLoc x
expLoc (EAbs elim zs) = expLoc (snd(head zs))
expLoc (ETuple xs) = expLoc (head xs)
expLoc (EIn _ x) = expLoc x
expLoc (ELet d x) = decLoc d
expLoc (EMend s elim e ms) = expLoc e

patLoc (PVar nm _) = loc nm
patLoc (PLit pos c) = pos
patLoc (PTuple []) = noPos
patLoc (PTuple ps) = patLoc (head ps)
patLoc (PCon (Nm(c1,p)) ps) = p
patLoc (PWild pos) = pos

decLoc (Def pos pat exp) = pos
decLoc (DataDec pos t args cs derivs) = pos
decLoc (GADT pos t k cs derivs ) = pos
decLoc (FunDec pos nm ts cls) = pos
decLoc (Synonym pos nm xs e) = pos

texpLoc:: TExpr -> SourcePos
texpLoc (TELit p l) = p
texpLoc (TEVar (Nm(nm,pos)) sch) = pos
texpLoc (TECon _ (Nm(nm,pos)) ty arity xs) = pos
texpLoc (TEApp x y) = texpLoc x
texpLoc (TEAbs elim zs) = texpLoc (snd(head zs))
texpLoc (TETuple xs) = texpLoc (head xs)
texpLoc (TEIn _ x) = texpLoc x
texpLoc (TEMend tag elim arg ms) = texpLoc arg
texpLoc (AppTyp e ty) = texpLoc e
texpLoc (AbsTyp s e) = texpLoc e
texpLoc (TECast p e) = texpLoc e
texpLoc (ContextHole e1 e2) = texpLoc e1
texpLoc (Emv _) = noPos
texpLoc x = noPos

elimLoc ElimConst = noPos
elimLoc (ElimFun [] t) = typLoc t
elimLoc (ElimFun (n:ns) _) = loc n

locL fpos [] = fpos
locL fpos (p:ps) = loc p

---------------------------------------------------
-- Some common types
---------------------------------------------------

tupleT [] = error "Tuple of width 0"
tupleT [t] = t
tupleT ts = TyTuple Star ts
   
-- arrT x y = TyApp (TyApp tarr x) y       
arrT x y = TyArr x y
pairT x y = TyTuple Star [x,y] -- TyApp (TyApp tpair x) y
listT x = TyApp tMu (TyApp tL x)
setT x = TyApp tset x
stringT = listT tchar
eitherT x y = TyApp (TyApp teither x) y
ioT x = TyApp tio x
maybeT x = TyApp tmaybe x

applyT [] = tunit
applyT [t] = t
applyT (t:s:ts) = applyT (TyApp t s : ts)


tMu      = TyMu Star   -- TyCon None (pre "Mu")      (PolyK [] (Karr (Karr Star Star) Star))
tL       = TyCon None (pre "L")       (PolyK [] (Karr Star  (Karr Star Star)))
tset     = TyCon None (pre "Set")     (PolyK [] (Karr Star  Star))
-- tpair    = TyCon None (pre "(,)")     (PolyK [] (Karr Star (Karr Star Star)))
-- tarr     = TyCon None (pre "(->)")    (PolyK [] (Karr Star (Karr Star Star)))
tmonad   = TyCon None (pre "Monad")   (PolyK [] (Karr (Karr Star Star) Star))
tbool    = TyCon None (pre "Bool")    (PolyK [] Star)
teither  = TyCon None (pre "Either")  (PolyK [] (Karr Star (Karr Star Star)))
tmaybe   = TyCon None (pre "Maybe")   (PolyK [] (Karr Star Star))
tinteger = TyCon None (pre "Integer") (PolyK [] Star)
tint     = TyCon None (pre "Int")     (PolyK [] Star)
tdouble  = TyCon None (pre "Double")  (PolyK [] Star)
tchar    = TyCon None (pre "Char")    (PolyK [] Star)
tunit    = TyCon None (pre "()")      (PolyK [] Star)
tio      = TyCon None (pre "IO")      (PolyK [] (Karr Star Star))
tstring = listT tchar

nat = (TyApp (TyMu Star) (TyCon (Syn "Nat") (toName "N") (PolyK [] (Karr Star Star))))

toTyp Int = tint
toType Char = tchar
toType Double = tdouble
toType Integer = tinteger
toType Unit = tunit

ta = TyVar (pre "a") Star
tb = TyVar (pre "b") Star
tc = TyVar (pre "c") Star

predefinedTyCon = 
   [("Int",tint)
   ,("Integer",tinteger)
   ,("Double",tdouble)
   ,("Char",tchar)
   ,("()",tunit)
   ,("IO",tio)
 --  ,("(->)",tarr)
   ]

---------------------------------------------------------
-- Partial imlementation of effect freesubstitution

lookT x xs def =
  case lookup x xs of
    Nothing -> def
    Just(Type t) -> t
    Just( x ) -> error ("Wrong class in lookT")

lookK x xs def =
  case lookup x xs of
    Nothing -> def
    Just(Kind k) -> k
    Just( x ) -> error ("Wrong class in lookK")
    
lookE x xs def =
  case lookup x xs of
    Nothing -> def
    Just(Exp k) -> k
    Just( x ) -> error ("Wrong class in lookE")    

pureSubKind :: [(Name,Class Kind Typ TExpr)] -> Kind -> Kind
pureSubKind env Star = Star
pureSubKind env (LiftK t) = LiftK(pureSubTyp env t)
pureSubKind env (Karr f x) = Karr(pureSubKind env f) (pureSubKind env x)
pureSubKind env (Kname n) = lookK n env (Kname n)
pureSubKind env (Kvar x) = Kvar x

pureSubPoly :: [(Name,Class Kind Typ TExpr)] -> PolyKind -> PolyKind
pureSubPoly env x = x  -- All PolyKinds should be closed terms

pureSubTerm :: [(Name,Class Kind Typ TExpr)] ->  Term -> Term
pureSubTerm env (Checked t) = Checked(pureSubTExpr env t)
pureSubTerm env (Parsed t) =  error ("No Parsed yet")
pureSubTerm env (Pattern p) =  error ("No Pattern yet")

pureSubTExpr :: [(Name,Class Kind Typ TExpr)] -> TExpr -> TExpr
pureSubTExpr env (TELit p l) = TELit p l
pureSubTExpr env (TEVar nm sch) = lookE nm env  (TEVar nm (pureSubScheme env sch))
pureSubTExpr env (TECon mu c ty arity xs) = TECon mu c ty arity (map (pureSubTExpr env) xs)
pureSubTExpr env (TEApp x y) = TEApp (pureSubTExpr env x) (pureSubTExpr env y)
pureSubTExpr env (TETuple xs) = TETuple (map (pureSubTExpr env) xs)
pureSubTExpr env (TEIn k x) = TEIn (pureSubKind env k) (pureSubTExpr env x)
pureSubTExpr env (TEAbs elim zs) = pureSubTExpr env (snd(head zs))
pureSubTExpr env (AppTyp e ty) = AppTyp (pureSubTExpr env e) (map (pureSubTyp env) ty)
pureSubTExpr env (AbsTyp tele e) = error ("No AbsTyp in pureSubTExpr yet")
pureSubTExpr env (Emv (u,p,t)) = Emv (u,p,pureSubTyp env t)
pureSubTExpr env (CSP x) = (CSP x)
pureSubTExpr env (ContextHole x y) = ContextHole (pureSubTExpr env x) (pureSubTExpr env y)
pureSubTExpr env x = error ("No pureSubTExpr yet: "++show x)

pureSubTyp :: [(Name,Class Kind Typ TExpr)] -> Typ -> Typ
pureSubTyp env (typ@(TyVar s k)) = lookT s env (TyVar s (pureSubKind env k))
pureSubTyp env (TyApp f x) = TyApp (pureSubTyp env f) (pureSubTyp env x)
pureSubTyp env (TyTuple k xs) = TyTuple k (map (pureSubTyp env) xs)
pureSubTyp env (TyCon mu c k) = TyCon mu c (pureSubPoly env k)
pureSubTyp env (TyProof f x) = TyProof (pureSubTyp env f) (pureSubTyp env x)
pureSubTyp env (TyArr f x) = TyArr (pureSubTyp env f) (pureSubTyp env x)
pureSubTyp env (TySyn nm n ts t) = TySyn nm n (map (pureSubTyp env) ts) (pureSubTyp env t)
pureSubTyp env (TyMu k) = TyMu (pureSubKind env k)
pureSubTyp env (TcTv (uniq,ptr,k)) = TcTv (uniq,ptr,pureSubKind env k)
pureSubTyp env (TyLift e) = TyLift (pureSubTerm env e)
pureSubTyp env (x@(TyAll vs t)) =  error ("No TyAll inpureSubTyp yet: "++show x)
 
pureSubRho env (Tau x) = Tau (pureSubTyp env x)
pureSubRho env (Rarr s r) = Rarr(pureSubScheme env s) (pureSubRho env r)

pureSubScheme env (Sch vs r) = error ("No pureSubScheme yet")
       -- Sch vs (pureSubRho env r)

rhoToTyp (Tau t) = t
rhoToTyp (Rarr s r) = TyArr (schemeToTyp s) (rhoToTyp r)

schemeToTyp (Sch [] r) = rhoToTyp r
schemeToTyp (Sch vs r) = TyAll vs (rhoToTyp r)
       
--------------------------------------------------------------
data TEqual where
  TRefl :: Typ -> TEqual
  TCong:: TEqual -> TEqual -> TEqual   --  App:: (f >= g) (x >= y) -> (f x) >= (g y)  | positive f g
  TArrCong:: TEqual -> TEqual -> TEqual 
  TProofCong:: TEqual -> TEqual -> TEqual 
  TTupleCong:: [TEqual] -> TEqual
  TSpec:: Typ -> [Typ] -> TEqual
  TGen:: Telescope -> TEqual -> TEqual
  TVar:: (Uniq,Pointer TEqual) -> TEqual
  TJoin:: TExpr -> TEqual  -- zero or more context holes
  TComp:: TEqual -> TEqual -> TEqual
  TSym:: TEqual -> TEqual

 
-------------------------------------------------------
--  TEqual justifies that two type-Schemes are equal
-- but we have to convert both Tau and Rho into Scheme

mono:: Typ -> Scheme
mono t = Sch [] (Tau t)

monoR r = Sch [] r

-- visualizing what a piece of evidence justifies as convertible

visualT (TRefl t) = (t,t)
visualT (TCong x y) = (TyApp f m,TyApp g n) 
  where (f,g) = visualT x
        (m,n) = visualT y
visualT (TProofCong x y) = (TyProof f m,TyProof g n) 
  where (f,g) = visualT x
        (m,n) = visualT y        
visualT (TArrCong x y) = (TyArr f m,TyArr g n) 
  where (f,g) = visualT x
        (m,n) = visualT y       
visualT (TTupleCong xs) = (TyTuple Star (map fst pairs),TyTuple Star (map snd pairs))
  where pairs = map visualT xs
visualT (TGen cs t) = (a,TyAll cs b) 
  where (a,b) = visualT t  
visualT (TVar (u,p)) = ((TyVar name Star),(TyVar name Star))
  where name = toName ("?"++show u)
visualT (TSpec (tyall@(TyAll tele body)) ts) = (tyall,pureSubTyp env body)
  where check [] [] = []
        check ((nm,Type k):xs) (t: ts) = (nm,Type t): check xs ts -- invariant (t:: k)
        check ((nm,Exp t):xs)  (TyLift(Checked e): ts) = (nm,Exp e): check xs ts
        check ((nm,Exp t):xs)  (w:ts) = (nm,Exp(TEVar(toName("???"++show w)) undefined)) : check xs ts
        check ((nm,Kind k):xs) (t: ts) = error("\nVisualT "++show k++" : "++show t)
        check w zz = error ("Arity doesn't match in visualT TSpec\n"++show tyall++"\n"++show ts++show w++"\n"++show zz)
        env = check tele ts
visualT (TJoin e2) = ((TyLift(Checked x)),(TyLift(Checked y)))
  where (x,y) = split e2
visualT (TComp x y) = (a,d)
  where (a,b) = visualT x
        (c,d) = visualT y  
visualT (TSym x) = (b,a) where (a,b) = visualT x          


ppTEqual p x = PP.vcat [ppTyp p a, PP.nest 3 (text "==>"),ppTyp p b]
  where (a,b) = visualT x
  
instance Show TEqual where
  show x = render(ppTEqual pi0 x)

-- smart constructors

tComp (TRefl t) x = x
tComp x (TRefl t) = x
tComp x y = TComp x y

tSym (TRefl x) = TRefl x
tSym x = TSym x

tCong (TRefl f) (TRefl x) = TRefl(TyApp f x)
tCong x y = TCong x y

tProof (TRefl f) (TRefl x) = TRefl(TyApp f x)
tProof x y = TProofCong x y

tArrCong (TRefl f) (TRefl x) = TRefl( TyArr f x )
tArrCong x y = TArrCong x y

tTupleCong xs | Just ts <- allRefl xs = TRefl(TyTuple Star ts)
  where allRefl [] = return []
        allRefl (x:xs) = do { ys <- allRefl xs
                            ; case x of
                                TRefl y -> return(y:ys)
                                _ -> Nothing }
tTupleCong xs = TTupleCong xs

tRefl x = TRefl x

tSpec (Sch [] rho) [] = TRefl (rhoToTyp rho)
tSpec sch ts = help (schemeToTyp sch) ts
  where help (TyAll [] rho) [] = TRefl rho
        help poly ts = TSpec poly ts

tGen [] x = x
tGen bs x = TGen bs x

teCast (TRefl t) e = e
teCast p e = TECast p e


spread1 f (x,y) =(f x,f y)       
spread2 f (x,y) (a,b) = (f x a,f y b)

split (ContextHole e1 e2) = (e1,e2)
split (TEApp x y) = spread2 TEApp (split x) (split y)
split (TETuple xs) = spread1 TETuple (map fst pairs,map snd pairs)
  where pairs = map split xs
split (TECon mu c ty arity xs) = spread1 (TECon mu c ty arity) (map fst pairs,map snd pairs)
   where pairs = map split xs
split (TEIn k x) = spread1 (TEIn k) (split x) 
split (AppTyp e ty) = split e
split (AbsTyp tele e) = split e
split (TECast p x) = split x
split x = (x,x)


nosplit (TELit _ _) = True
nosplit (TEVar _ _) = True
nosplit (TECon mu c ty arity xs) = all nosplit xs
nosplit (TEApp x y) = (nosplit x) && (nosplit y)
nosplit (TETuple xs) = all nosplit xs
nosplit (TELet _ _) = error ("No TLet in nosplit yet")
nosplit (TEIn k x) = (nosplit x) 
nosplit (TEMend _ _ _ _) = error ("No TEMend in nosplit yet")
nosplit (AppTyp e ty) = nosplit e
nosplit (AbsTyp tele e) = nosplit e
nosplit (TECast p x) = nosplit x
nosplit (Emv _) = True
nosplit (CSP _) = True
nosplit (ContextHole _ _) = False

 