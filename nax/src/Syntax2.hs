{-# LANGUAGE RankNTypes, GADTs, FlexibleInstances #-}

module Syntax2 where

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


---------------------------------------------------
-- data types that are parsed

data Quant = UNIV | GLOBAL deriving (Show,Eq)

data PExpr
   = PELit SourcePos Literal  -- 5, 2.3, "abc", etc.
   | PEVar Quant Name         -- x , `succ
   | PECon Name               -- Cons, Nil
   | PEApp PExpr PExpr        -- e1 e2                           
   -- PEAbs will eventually be retired
   | PEAbs (Elim [Name]) [(Pat Name PTyp,PExpr)]  -- (\ {i.Odd i} x -> f[x]+1)        
   | PELam (Pat Name PTyp) PExpr
   | PECase (Elim [Name]) PExpr [(Pat Name PTyp,PExpr)]   
   | PETuple [PExpr]
   | PELet (Decl PExpr) PExpr
   | PEIn Kind PExpr
   | PEMend String (Elim [Typ]) PExpr [([Pat Name PTyp],PExpr)]
   
data PTyp 
   = PTyVar Name 
   | PTyApp PTyp PTyp
   | PTyIndex PTyp PExpr
   | PTyTuple [PTyp]  
   | PTyCon Name
   | PTyProof PTyp PTyp
   | PTyArr PTyp PTyp
   | PTyMu Kind
   | PTyAll [Name] PTyp 
   

---------------------------------------------------------
-- Terms

data TExpr 
   = TELit SourcePos Literal      -- 5, 2.3, "abc", etc.
   | TEVar Name Scheme            -- x , ?x1
   | TECon MuSyntax Name Rho Arity [TExpr]
   | TEApp (TExpr) (TExpr)        -- e1 e2                           
   | TEAbs (Elim Telescope) [(Pat Name Typ,TExpr)]     -- (\ x -> f[x]+1)   
   | TELam (Pat Name Typ) TExpr
   | TECase (Elim [Name]) TExpr [(Pat Name Typ,TExpr)]
   | TETuple [TExpr]              -- (5,True,"asd")
   | TELet (Decl (TExpr)) (TExpr)
   | TEIn Kind TExpr
   | TEMend String (Elim (Telescope,[(Typ,Kind)])) (TExpr) [([Pat Name Typ],TExpr)]
   | AppTyp (TExpr) [Typ]
   | AbsTyp Telescope TExpr
   | Emv (Uniq,Pointer (TExpr),Typ)  -- Typ has to be first order, I.e. data, not a function.
   | CSP (Name,Integer,Value IO) 

data Pat n t
   = PVar n
   | PLit SourcePos Literal
   | PTuple [Pat n t]
   | PCon Name [Pat n t]
   | PWild SourcePos
   | PTyp (Pat n t) t

   

data Decl e 
   = Def SourcePos (Pat Name Typ) e
   | DataDec SourcePos Name [Name] [(Name,[Scheme])] [Derivation]
   | GADT SourcePos Name [Name] Kind [(Name,[Name],[Scheme],Rho)] [Derivation]
   | FunDec SourcePos String [(Name,Kind)] [([Pat Name Typ],e)]
   | Synonym SourcePos Name [Name] Typ -- This Typ is interpreted as a pattern

data Prog m = Prog [Decl m]

data Elim nms = ElimFun nms Typ | ElimConst

data Class k t e = Kind k | Type t | Exp e


patBinds:: Ord n => Pat n t -> [n] -> [n]
patBinds (PVar n) bound = (insert n bound)
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
data Term = Parsed PExpr | Checked TExpr | Pattern (Pat Name Typ)

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
   | TPLift (Pat Name Typ)

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
 
instance Eq nm => Eq (Pat nm ty) where
  (PVar x) == (PVar y) = x==y
  (PLit _ x) == (PLit _ y) = x==y
  -- (PSum i x)== (PSum j y) = i==j && x==y
  (PTuple xs) == (PTuple ys) = xs == ys
  (PWild _) == (PWild _) = True
  (PCon c xs) == (PCon d ys) = c==d && xs == ys
  _ == _ = False
  
instance Eq PExpr where
  (PELit _ x) == (PELit _ y) = x==y
  (PEVar q1 (Nm(x,_))) == (PEVar q2 (Nm(y,_))) = q1==q2 && x==y
  (PECon n) == (PECon m) = n==m 
  (PEApp x y) == (PEApp a b) = x==a && y==b  
  (PEAbs _ _) == (PEAbs _ _) = error "No Abs instance in (Eq Expr) yet."
  (PELam _ _) == (PELam _ _) = error "No Lam instance in (Eq Expr) yet."
  (PECase _ _ _) == (PECase _ _ _) = error "No Case instance in (Eq Expr) yet."  
  (PETuple xs) == (PETuple ys) = xs == ys
  (PELet x y) == (PELet m n) = error "No Let in instance (Eq Expr) yet."
  (PEIn k1 x) == (PEIn k2 y) = k1==k2 && x==y
  (PEMend tag1 e1 arg1 cs1) == (PEMend tag2 e2 arg2 cs2) = error "No EMend in instance (Eq Expr) yet."
  _ == _ = False
  
instance Eq TExpr where
  (TELit _ x) == (TELit _ y) = x==y
  (TEVar(Nm(x,_)) sch1) == (TEVar(Nm(y,_)) sch2) = x==y
  (TECon _ n _ a1 xs) == (TECon _ m _ a2 ys) = n==m && xs==ys && a1==a2
  (TEApp x y) == (TEApp a b) = x==a && y==b  
  (TEAbs e1 ms1) == (TEAbs e2 ms2) = error "No Abs in instance (TEq Expr) yet."
  (TELam p1 e1) == (TELam p2 e2) = error "No Lam in instance (TEq Expr) yet."
  (TECase el1 e1 m1) == (TECase el2 e2 m2) = error "No Case in instance (TEq Expr) yet."
  (TETuple xs) == (TETuple ys) = xs == ys
  (TELet x y) == (TELet m n) = error "No Let in instance (TEq Expr) yet."
  (TEIn k1 x) == (TEIn k2 y) = k1==k2 && x==y
  (TEMend tag1 e1 arg1 cs1) == (TEMend tag2 e2 arg2 cs2)  = error "No EMend in instance (TEq Expr) yet."
  (AppTyp x y) == (AppTyp a b) = x==a && y==b  
  (AbsTyp x y) == (AbsTyp a b) = error "No ETyAbs in instance (TEq Expr) yet."
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
equalTyp s t = False


-------------------------------------------------------------
-- special syntax recognizers

toBinary f [x] = (PEApp f x)
toBinary f (x:xs) = toBinary (PEApp f x) xs

fromBinary:: PExpr -> (PExpr,[PExpr])
fromBinary (PEApp f x) = (g,ys++[x]) where (g,ys) = fromBinary f
fromBinary f = (f,[])

fromTBinary:: TExpr -> (TExpr,[TExpr])
fromTBinary (TEApp f x) = (g,ys++[x]) where (g,ys) = fromTBinary f
fromTBinary f = (f,[])

--- Rcognizing Char
isExprChar (PELit _ (LChar _)) = True
isExprChar _ = False

isTExprChar (TELit _ (LChar _)) = True
isTExprChar _ = False

isValueChar (VBase _ (LChar _)) = True
isValueChar _ = False

charExprOf (PELit _ (LChar c)) = c
charTExprOf (TELit _ (LChar c)) = c
charValueOf (VBase _ (LChar c)) = c  

--- recogizing Lists

isExprList (PEApp (PEApp (PEVar _ (Nm("Cons",_))) x) (PEIn Star y))
   = do { ys <- isExprList y; return (x:ys)}
isExprList (PEVar _ (Nm("Nil",_))) = Just []
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

ppList :: (PExpr -> Doc) -> [PExpr] -> Doc
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

data PI = PI { synonymInfo :: [Typ -> Maybe Typ] }

pi0 = PI [listSyn,natSyn]

listSyn (typ@(TyApp (TyMu Star) (TyApp (TyCon _ (Nm("L",_)) k) x))) = Just(TySyn (toName "List") 1 [x] typ)
listSyn _ = Nothing

natSyn (typ@(TyApp (TyMu Star)(TyCon _ (Nm("N",_)) k))) = Just(TySyn (toName "Nat") 0 [] typ)
natSyn _ = Nothing




----------------------------------------------------
-- Parenthesizing things

parenExpr:: PI -> PExpr -> Doc
parenExpr p (x @ (PEVar _ _)) = ppExpr p x
parenExpr p (x @ (PELit _ _)) = ppExpr p x
parenExpr p (x @ (PETuple _)) = ppExpr p x
parenExpr p (PEIn Star x) | Just ys <- isExprList x  = ppList (ppExpr p) ys
parenExpr p (x @ (PEIn _ _)) = ppExpr p x
parenExpr p (x @ (PECon _)) = ppExpr p x
parenExpr p x = PP.parens $ ppExpr p x  

noParenOnApply:: PI -> PExpr -> Doc
noParenOnApply p (x@(PEApp _ _)) = ppExpr p x
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

parenPTypArrow p (w@(PTyArr x y)) = PP.parens (ppPTyp p w)
parenPTypArrow p w = ppPTyp p w

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


needsPParens (PTyTuple _) = False 
needsPParens (PTyArr _ _) = True
needsPParens (PTyApp _ _) = True
needsPParens _ = False
----------------------------------------------------------------------
-- Pretty printing Expr, and various strategies for parenthesizing

ppExpr:: PI -> PExpr -> Doc
ppExpr p e =
  case e of
    (PELit pos l) -> ppLit l
    (PEVar UNIV (Nm(v,pos))) -> text v
    (PEVar GLOBAL (Nm(v,pos))) -> text("`"++v)
    (PECon (Nm(v,pos))) -> text v


{-
    (PEApp (PEAbs e1 ms) e) -> 
       (text "case" <> ppElim p e1 <+> parenExpr p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppNameWithP ppPTyp ppExpr) ms)))
-}

    (term@(PEApp (PEApp (PEVar _ (Nm(f,pos))) x) y))
       | infixp f -> PP.sep [(noParenOnApply p x),text f,noParenOnApply p y]
    (term@(PEApp _ _)) -> ppSepBy (noParenOnApply p f : (map (parenExpr p) xs)) " "
      where (f,xs) = fromBinary term
      
    (PEAbs elim ms) -> ((text "\\" <> ppElim p elim) $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppNameWithP ppPTyp ppExpr) ms))))                 



    (PELam pat ms) -> 
        PP.sep [ text "\\" <+> ppPat2 ppNameWithP ppPTyp p pat
               , text "->" 
               , PP.nest 2 (ppExpr p ms) ]
    (PECase elim e ms) -> 
       (text "case" <+> parenExpr p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppNameWithP ppPTyp ppExpr) ms)))                

    (PETuple ps) -> ppSepByParen (map (ppExpr p) ps) "," 
    (e@(PELet _ _)) ->
        PP.vcat [text "let "<> ppDecl p ppExpr d
                , PP.nest 4 (PP.vcat(map (ppDecl p ppExpr) ds))
                ,text "in" <+> ppExpr p body]
      where (d:ds,body) = flatLet e []
    (PEIn Star x) | Just ys <- isExprList x -> ppList (ppExpr p) ys
    (PEIn k x) -> PP.sep[text "(In"<>PP.brackets(parensKindQ p k),ppExpr p x]<>text ")"

    (PEMend s elim exp ms) -> PP.vcat ((text s <> ppElim p elim <+> ppExpr p exp <+> text "where"): map f ms)
       where f (ps,body) = PP.nest 2(PP.sep[PP.hsep (map (ppPat2 ppNameWithP ppPTyp p) ps) <+> text "=",PP.nest 2 (ppExpr p body)])

ppNameWithP p x = ppName x

ppMatch p ppn ppt ppf (pat,body) = PP.sep [ppPat2 ppn ppt p pat <+> text "->",PP.nest 2 (ppf p body)]

flatLet (PELet d e) ds = flatLet e (d:ds)
flatLet e ds = (ds,e)
  
---------------------------------------------------------------------------------
-- TExpr

ppTExpr:: PI -> TExpr -> Doc
ppTExpr p e = 
  case e of
    (TELit pos l) -> ppLit l
    (TEVar (Nm(v,pos)) sch) -> text v
    (TECon mu (Nm(v,pos)) typ arity []) -> text v  -- <>PP.brackets(ppRho p typ)
    (TECon mu  (Nm(v,pos)) typ arity xs) -> PP.parens(PP.sep (text v : map (parenTExpr p) xs))<>text "'"
    (TEApp (TEAbs elim ms) e) -> 
       (text "case" <> ppElim p elim <+> parenTExpr p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppNameWithP ppTyp ppTExpr) ms)))
    (term@(TEApp (TEApp (TEVar (Nm(f,pos)) sch) x) y))
       | infixp f -> PP.sep [(noParenTExprApply p x),text f,noParenTExprApply p y]

    (term@(TEApp _ _)) -> ppSepBy (noParenTExprApply p f : (map (parenTExpr p) xs)) " "
      where (f,xs) = fromTBinary term
    (TEAbs e1 ms) -> ((text "\\"<> ppElim p e1) $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppNameWithP ppTyp ppTExpr) ms))))                 
                 
    (TELam pat ms) -> 
        PP.sep [ text "\\" <+> ppPat2 ppNameWithP ppTyp p pat
               , text "->" 
               , PP.nest 2 (ppTExpr p ms) ]
    (TECase elim e ms) -> 
       (text "case" <+> parenTExpr p e <+> text "of") $$
                 (PP.nest 2 (PP.vcat (map (ppMatch p ppNameWithP ppTyp ppTExpr) ms)))                

                 
    (TETuple ps) -> ppSepByParen (map (ppTExpr p) ps) "," 
    (e@(TELet _ _)) ->
        PP.vcat [text "let "<> ppDecl p ppTExpr d
                , PP.nest 4 (PP.vcat(map (ppDecl p ppTExpr) ds))
                ,text "in" <+> ppTExpr p  body]
      where (d:ds,body) = flatLet e []
            flatLet (TELet d e) ds = flatLet e (d:ds)
	    flatLet e ds = (ds,e)
    (TEIn Star x) | Just (a,ys) <- isTExprList x -> ppTList (ppTExpr p) ys
    (TEIn k (TECon (Syn d) c rho 0 [])) ->  text("`"++d)
    (TEIn k (TECon (Syn d) c rho arity xs)) -> 
        PP.parens(PP.sep(text ("`"++d) : map (ppTExpr p) xs))
    
    (TEIn k x) -> PP.sep[text "(In"<>PP.brackets(parensKindQ p k),ppTExpr p x]<>text ")"
    (TEMend s elim exp ms) -> PP.vcat ((text s <> ppElim p elim <+> ppTExpr p exp <+> text "where"): map f ms)
       where f (ps,body) = PP.nest 2(PP.sep[PP.hsep (map (ppPat p) ps) <+> text "=",PP.nest 2 (ppTExpr p body)])
    (AppTyp e ts) -> ppTExpr p e <> PP.brackets(ppSepBy (map (ppTyp p) ts) ",")
    (AbsTyp vs t) -> PP.parens (PP.sep [braces(PP.sep (ppKArgs p vs)) <+> text ".", ppTExpr p t])
    (Emv (uniq,ptr,k)) -> text("e"++show uniq)
    (CSP (nm,i,v)) -> text("`"++show nm)
    
ppTerm p (Parsed x) = ppExpr p x -- <> text "%"
ppTerm p (Checked x) = ppTExpr p x -- <> text "#" 
ppTerm p (Pattern x) = ppPat p x    -- <> text "&" 

---------------------------------------------------
-- Patterns

ppPat:: PI -> Pat Name Typ -> Doc
ppPat p pat =
  case pat of
    PLit p l -> ppLit l
    PVar v -> text (name v)
    PTuple ps -> ppSepByParen (map (ppPat p) ps) "," 
    PWild p -> text "_"
    -- PSum j p -> PP.parens(text (show j) <+> ppPat p)
    PCon (Nm(v,pos)) [] -> text v
    PCon (Nm(":",_)) (p1:ps) -> PP.parens $ ppPat p p1 <+> text  ":" <+> PP.hsep (map (ppPat p) ps)
    PCon (Nm(v,pos)) ps -> PP.parens $ text v <+> PP.hsep (map (ppPat p) ps)


ppPat2 pN pT p pat =
  case pat of
    PLit p l -> ppLit l   
    PVar v -> pN p v
    PWild p -> text "_"
    PCon v [] -> ppName v
    PCon v ps -> PP.parens $ ppName v <+> PP.hsep (map (ppPat2 pN pT p) ps)
    PTyp pat t -> PP.parens(ppPat2 pN pT p pat <> text ":" <> pT p t)


----------------------------------------------------------------    
 
ppDecl ::  PI -> (PI -> a -> Doc) -> Decl a -> Doc
ppDecl p ppf (Def _ pat exp) = PP.sep [ppPat p pat
                               ,PP.nest 3 (text "=")
                               ,PP.nest 3 (ppf p exp)]
ppDecl p ppf (FunDec _ nm ts cls) = PP.vcat(map (f ts) cls)
  where f ts (ps,e) = PP.sep [text nm <> args ts <> PP.hsep(map (ppPat p) ps) <+> text "=", PP.nest 2 (ppf p e)]
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
ppDecl p ppf (GADT pos nm free kind cs derivs) = 
     PP.vcat ((PP.sep[ text "gadt", ppName nm, text ":" , ppKindAll free, ppKind p kind, text "where"]) : 
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
        
  
ppPTyp p (PTyVar s) = ppName s
ppPTyp p (PTyApp f x) | needsPParens x = (ppPTyp p f) <+> (PP.parens (ppPTyp p x))
ppPTyp p (PTyApp f x) = (ppPTyp p f) <+> (ppPTyp p x)
ppPTyp p (PTyIndex f x) = (ppPTyp p f) <+> PP.braces(ppExpr p x)
ppPTyp p (PTyTuple ts) = PP.parens(PP.cat (PP.punctuate PP.comma (map (ppPTyp p) ts)))
ppPTyp p (PTyCon c) = ppName c  
ppPTyp p (PTyProof x y) = PP.parens (ppPTyp p x <> text "==" <> (ppPTyp p y))
ppPTyp p (PTyArr x y) =  PP.sep[parenPTypArrow p x <+> text "->",PP.nest 1 (ppPTyp p y)]
ppPTyp p (PTyMu Star) = text "Mu[*]"
ppPTyp p (PTyMu k) = text "Mu[" <> ppKind p k <> text "]"
ppPTyp p (PTyAll [] t) = ppPTyp p t
ppPTyp p (PTyAll nms t) = PP.parens(PP.sep[text "forall"
                                         ,PP.sep (map ppName nms) 
                                         ,text "."
                                         ,ppPTyp p t])


ppTyp :: PI -> Typ -> Doc
ppTyp p t | Just w <- isSyn p t = ppTyp p w
ppTyp p (TyVar s k) = ppName s

ppTyp p (f@(TyApp _ _)) | Just (syn,ts) <- shorthand f [] = ppTyp p (applyT (TyVar syn Star : ts))
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

shorthand (TyApp (TyMu k) args) ts = g args ts
   where g (TyCon (Syn l) c k) ts = return(toName l,ts)
         g (TyApp f t) ts = g f (t:ts)
         g _ ts = Nothing
shorthand (TyApp f t) ts = shorthand f (t:ts)
shorthand x ts = Nothing

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
ppValue p (v@(VIn k _)) | Just vs <- isValueList v = ppVList (ppValue p) vs
ppValue p (VIn k (VCon (Syn d) arity c [])) = text(d++"'")
ppValue p (VIn k (VCon (Syn d) arity c vs)) = 
   PP.parens(PP.sep(text (d++"'") : map (ppValue p) vs))
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
instance Show PTyp where
  show t = render(ppPTyp pi0 t)  
instance Show Kind where
  show t = render(ppKind pi0 t)
instance Show Scheme where
  show t = render(ppScheme pi0 t)
instance Show Rho where
  show r = render(ppRho pi0 r)
instance Show PExpr where
  show d = render(ppExpr pi0 d)
instance Show TExpr where
  show d = render(ppTExpr pi0 d)  
instance Show (Decl PExpr) where
  show d = render(ppDecl pi0 ppExpr d)
instance Show (Decl TExpr) where
  show d = render(ppDecl pi0 ppTExpr d)  
instance Show (Prog PExpr) where
  show (Prog xs) = render(PP.vcat(map h xs))
    where h x = PP.vcat[ppDecl pi0 ppExpr x,text ""]
instance Show (Prog TExpr) where
  show (Prog xs) = render(PP.vcat(map h xs))
    where h x = PP.vcat[ppDecl pi0 ppTExpr x,text ""]    
    
instance Show (Pat Name Typ) where
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

mapMDecl :: Monad m => (t -> m a) -> Decl t -> m (Decl a)
mapMDecl f (Def loc p e) = do { e2 <- f e; return(Def loc p e2)}
mapMDecl f (DataDec loc nm args cs derivs) = return(DataDec loc nm args cs derivs)
mapMDecl f (GADT loc nm free kind cs derivs) = return(GADT loc nm free kind cs derivs)
mapMDecl f (FunDec pos nm ts cls) = lift1 (FunDec pos nm ts) (mapM g cls)
  where g (ps,e) = do { e2 <- f e; return(ps,e2)}
mapMDecl f (Synonym pos nm xs typ) = return(Synonym pos nm xs typ)

mapDecl f x = runId (mapMDecl (return . f) x)
      

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
toPat (TyLift x) = error ("Non pattern in TyLift in Type Pattern context: "++show x)

 
----------------------------------------------
-- locations 
----------------------------------------------

instance Loc PExpr where loc = expLoc
instance Loc TExpr where loc = texpLoc
instance Loc nm => Loc (Pat nm ty) where loc = patLoc
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


kindLoc Star = noPos
kindLoc (LiftK t) = typLoc t
kindLoc (Karr k1 k2) = bestPos (kindLoc k1) (kindLoc k2)
kindLoc (Kvar _) = noPos
kindLoc (Kname (Nm(_,p))) = p

expLoc:: PExpr -> SourcePos
expLoc (PELit p l) = p
expLoc (PEVar _ (Nm(nm,pos))) = pos
expLoc (PECon (Nm(nm,pos))) = pos
expLoc (PEApp x y) = expLoc x
expLoc (PEAbs elim zs) = expLoc (snd(head zs))
expLoc (PELam p e) = bestPos (patLoc p) (expLoc e)
expLoc (PECase el e ms) = expLoc e
expLoc (PETuple xs) = expLoc (head xs)
expLoc (PEIn _ x) = expLoc x
expLoc (PELet d x) = decLoc d
expLoc (PEMend s elim e ms) = expLoc e

patLoc (PVar nm) = loc nm
patLoc (PLit pos c) = pos
patLoc (PTuple []) = noPos
patLoc (PTuple ps) = patLoc (head ps)
patLoc (PCon (Nm(c1,p)) ps) = p
patLoc (PWild pos) = pos

decLoc (Def pos pat exp) = pos
decLoc (DataDec pos t args cs derivs) = pos
decLoc (GADT pos t free k cs derivs ) = pos
decLoc (FunDec pos nm ts cls) = pos
decLoc (Synonym pos nm xs e) = pos

texpLoc:: TExpr -> SourcePos
texpLoc (TELit p l) = p
texpLoc (TEVar (Nm(nm,pos)) sch) = pos
texpLoc (TECon _ (Nm(nm,pos)) ty arity xs) = pos
texpLoc (TEApp x y) = texpLoc x
texpLoc (TEAbs elim zs) = texpLoc (snd(head zs))
texpLoc (TELam p e) = bestPos (patLoc p) (texpLoc e)
texpLoc (TECase el e ms) = texpLoc e
texpLoc (TETuple xs) = texpLoc (head xs)
texpLoc (TEIn _ x) = texpLoc x
texpLoc (TEMend tag elim arg ms) = texpLoc arg
texpLoc (AppTyp e ty) = texpLoc e
texpLoc (AbsTyp s e) = texpLoc e
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


ptunit = PTyCon (pre "()") 


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

