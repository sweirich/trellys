{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeSynonymInstances  #-}

module Language.SepCore.Syntax(
     Logicdecl(..), Stage(..), SuperKind(..),
     LogicalKind(..), Predicate(..), Proof(..),
     Term(..), Arg(..), ArgName(..), ArgClass(..),
     Value(..), Equality(..), TypingContext, Proofdef(..),
     Progdecl(..), Progdef(..), Preddecl(..), Preddef(..), Datatypedecl(..), Declaration(..),Module(..), Scheme(..), TermBranches(..), Tele(..), Expr(..)
                               ) where 
import Language.SepCore.Lexer
import Language.SepCore.PrettyPrint
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Alpha(aeqR1)
import Unbound.LocallyNameless.Subst(substR1)
import Text.PrettyPrint
type Module = [Declaration] 

data Declaration = DeclLogic Logicdecl
                 | DeclProof Proofdef
                 | DeclProgdecl Progdecl           
                 | DeclProgdef Progdef
                 | DeclPreddef Preddef
                 | DeclPreddecl Preddecl
                 | DeclData Datatypedecl
                   deriving(Show)

data Logicdecl = Logicdecl Proof Predicate 
             deriving (Show)

data Proofdef = Proofdef Proof Proof 
             deriving (Show)

data Progdecl = Progdecl Term Term
             deriving(Show)

data Progdef = Progdef Term Term
             deriving(Show)

data Preddecl = Preddecl Predicate LogicalKind
             deriving(Show)

data Preddef = Preddef Predicate Predicate
             deriving(Show)

data Tele = Empty 
          | TCons (Rebind (ArgName,Stage,Embed ArgClass) Tele) 
          deriving (Show)

data Datatypedecl = Datatypedecl String (Bind Tele [(String,Term)])    
                    deriving (Show)

-- | I define expr data for display purpose only.
data Expr = ExprTerm Term
          | ExprProof Proof
          | ExprPred Predicate
          | ExprLK LogicalKind
            deriving(Show)
instance Disp Expr where
  disp (ExprTerm t) = disp t
  disp (ExprProof p) = disp p
  disp (ExprPred p) = disp p
  disp (ExprLK p) = disp p
  
-- data Datatypedecl = Datatypedecl Term Term [(Term, Term)]
--              deriving(Show)
-- data Sepcialterm = Specialterm Term 
--                  deriving(Show)

      
data Stage = Plus | Minus deriving(Show)

data SuperKind = Logical Integer 
                deriving (Show)

data LogicalKind = Formula Integer

         | QuasiForall (Bind (ArgName, Embed ArgClass) LogicalKind)

         | PosLK AlexPosn LogicalKind
           
  deriving(Show)

data Predicate = PredicateVar (Name Predicate)

           | PredicateLambda (Bind (ArgName, Embed ArgClass) Predicate)

           | PredicateApplication Predicate Arg

           | Forall (Bind (ArgName, Embed ArgClass) Predicate)

           | PredicateLetProof (Bind (Name Proof) Predicate) Proof

           | PredicateLetPredicate (Bind (Name Predicate) Predicate) Predicate

           | PredicateLetTerm (Bind (Name Term, Name Proof) Predicate) Term

           | Equal Term Term

           | Terminate Term

           | Disjunction Predicate Predicate

           | Exist (Bind (ArgName, Embed ArgClass) Predicate)

           | Bottom Integer

           | Order Term Term
            
           | PosPredicate AlexPosn Predicate
  deriving(Show)

data Proof =  ProofVar (Name Proof)

             | InjectLeft Proof Predicate

             | InjectRight Proof Predicate

             | DisjunctionElimination (Bind (Name Proof) Proof) (Bind (Name Proof) Proof) Proof
             
             | ProofLambda (Bind (ArgName, Embed ArgClass) Proof)

             | ProofApplication Proof Arg

             | ExistentialIntroduction (Arg, Proof) Predicate

             | ExistentialElimination Proof (Bind (ArgName, Name Predicate) Proof)

             | ProofLetProof (Bind (Name Proof) Proof) Proof

             | ProofLetPredicate (Bind (Name Predicate) Proof) Predicate

             | ProofLetTerm (Bind (Name Term, Name Proof) Proof) Term --Bind a term var and a proof var in a proof.

             | Join Term Term

             | ConvProof Proof [Equality] (Bind [(Name Term)] Predicate) 

             | Valax Term

             | ProofOrder Term Term

             | ProofCase Term Proof (Bind (Name Proof)  [(Term, [ArgName],Proof )])
 
             | TerminationCase Term (Bind (Name Proof) (Proof,Proof)) 

             | Ind (Bind (Name Term, Name Proof, Embed Term, Name Proof) Proof)

--bind three variable in a proof

             | Contra Proof
            
             | Contraval Proof Proof
            
             | PosProof AlexPosn Proof

    deriving(Show)

type Scheme = [(ArgName,Stage)]

type TermBranches = [(String,(Bind Scheme Term))]

-- type TermBranches = [(TermScheme,Term)]

data Equality = Equality Predicate
            
              | EqualityProof Proof

    deriving(Show)    

data Term =  TermVar (Name Term)

           | Type Integer

           | Pi (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermLambda (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermLetTerm (Bind (Name Term, Name Proof) Term) Term
           
           | TermLetTerm1 (Bind (Name Term) Term) Term
             
           | TermLetProof (Bind (Name Proof) Term) Proof

           | TermLetPredicate ((Bind (Name Predicate) Term)) Predicate

           | ConvTerm Term [Equality] (Bind [(Name Term)] Term)

           | Conv Term Proof (Bind [(Name Term)] Term)

           | TermCase Term (Bind (Name Term)  [(Term, [ArgName],Term)])

           | TermCase1 Term TermBranches

           | Tcast Term Proof

           | TermApplication Term Arg Stage

           | DataConstr String
             
           | DataType String

           | Abort Term

           | Rec (Bind (Name Term, Name Term, Embed Term) Term)
           
           | Undefined

           | Pos AlexPosn Term 
--bind two term in a term.

  deriving(Show)

data ArgClass = ArgClassTerm Term

               | ArgClassPredicate Predicate

               | ArgClassLogicalKind LogicalKind

      deriving(Show)

data Arg = ArgTerm Term

          | ArgProof Proof

          | ArgPredicate Predicate

        deriving(Show)

data ArgName = ArgNameProof (Name Proof)
           
          | ArgNameTerm (Name Term)
        
          | ArgNamePredicate (Name Predicate)   

         deriving (Show, Eq, Ord)


data Value = Value | NonValue deriving (Show)


         

$(derive [''Proof,''Term, ''Predicate, ''Arg, ''ArgName, ''Stage, ''Value, ''ArgClass, ''LogicalKind, ''Equality, ''Tele, ''Declaration, ''Logicdecl, ''Progdecl, ''Preddef, ''Proofdef,''Preddecl, ''Datatypedecl, ''Progdef, ''AlexPosn])

type TypingContext = [(ArgName, ArgClass,Value )]

instance Subst LogicalKind Stage
instance Subst LogicalKind ArgName
instance Subst LogicalKind Value
instance Subst LogicalKind Arg
instance Subst LogicalKind ArgClass
instance Subst LogicalKind Predicate
instance Subst LogicalKind Term
instance Subst LogicalKind Proof
instance Subst LogicalKind LogicalKind
instance Subst LogicalKind Equality

instance Subst Arg Stage
instance Subst Arg ArgName
instance Subst Arg ArgClass
instance Subst Arg LogicalKind
instance Subst Arg Arg 

instance Subst Arg Predicate where
  subst n (ArgPredicate pd) prd = subst (translate n) pd prd
  subst n a prd = substR1 rep1 n a prd

-- | here we do a implicit mutually recursive call on the 'substR1' defined in (Subst Arg Term) and (Subst Arg Proof)

instance Subst Arg Term where
  subst n (ArgTerm t) tm = subst (translate n) t tm
  subst n a tm = substR1 rep1 n a tm

instance Subst Arg Proof where
  subst n (ArgProof p) pf = subst (translate n) p pf
  subst n a pf = substR1 rep1 n a pf

instance Subst Arg Equality

instance Subst Proof Arg
instance Subst Proof ArgName
instance Subst Proof Term 
instance Subst Proof Predicate 
instance Subst Proof Stage
instance Subst Proof LogicalKind
instance Subst Proof Value
instance Subst Proof ArgClass
instance Subst Proof Equality
instance Subst Proof Proof where
  isvar (ProofVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Term Arg
instance Subst Term ArgClass
instance Subst Term ArgName
instance Subst Term Proof 
instance Subst Term Equality
instance Subst Term Predicate 
instance Subst Term LogicalKind
instance Subst Term Stage
instance Subst Term Value
instance Subst Term Term where
  isvar (TermVar x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Predicate Term 
instance Subst Predicate Proof
instance Subst Predicate Equality
instance Subst Predicate LogicalKind
instance Subst Predicate Stage
instance Subst Predicate Value
instance Subst Predicate Arg
instance Subst Predicate ArgClass
instance Subst Predicate ArgName
instance Subst Predicate Predicate where
        isvar (PredicateVar x) = Just (SubstName x)
        isvar _ = Nothing

instance Subst LogicalKind AlexPosn
instance Subst Arg AlexPosn
instance Subst Proof AlexPosn
instance Subst Term AlexPosn
instance Subst Predicate AlexPosn

instance Alpha AlexPosn
instance Alpha Equality
instance Alpha Predicate
instance Alpha Term where
  aeq' c (Pos _ t1) t2 = t1 `aeq` t2
  aeq' c t1 (Pos _ t2) = t1 `aeq` t2
  aeq' c t1 t2 = aeqR1 rep1 c t1 t2
instance Alpha Proof
instance Alpha LogicalKind
instance Alpha Stage
instance Alpha Value
instance Alpha ArgClass
instance Alpha Arg
instance Alpha ArgName
instance Alpha Tele

instance Alpha Declaration
instance Alpha Progdef
instance Alpha Progdecl
instance Alpha Logicdecl
instance Alpha Proofdef
instance Alpha Datatypedecl
instance Alpha Preddef
instance Alpha Preddecl


-- display elements
instance Disp Term where
  disp  = cleverDisp
instance Disp Proof where
  disp  = cleverDisp
instance Disp Predicate where
  disp  = cleverDisp
instance Disp LogicalKind where
  disp  = cleverDisp
instance Disp Stage where
  disp  = cleverDisp
instance Disp ArgClass where  
  disp  = cleverDisp
instance Disp Arg where
    disp  = cleverDisp
instance Disp ArgName where
    disp  = cleverDisp
instance Disp Declaration where
    disp  = cleverDisp
instance Disp Progdef where
    disp  = cleverDisp
instance Disp Progdecl where
    disp  = cleverDisp
instance Disp Logicdecl where
    disp  = cleverDisp
instance Disp Proofdef where
    disp  = cleverDisp
instance Disp Preddecl where
    disp  = cleverDisp
instance Disp Preddef where
    disp  = cleverDisp
instance Disp Tele where
    disp  = cleverDisp
instance Disp AlexPosn where
    disp (AlexPn _ line col) = disp line <> colon <> disp col <> colon

dParen:: (Display a) => Int -> a -> M Doc
dParen level x =
   if level >= (precedence x)
      then do { d <- display x; return(parens d)}
      else display x

termParen:: (Display a) => Int -> a -> M Doc
termParen level x =
   if level <= (precedence x)
      then do { d <- display x; return(parens d)}
      else display x

-- Set the precedence to i. If this is < than the current precedence, then wrap
-- this with parens.
-- withPrec:: Int -> m
-- withPrec i m = do
--   dm <- local (const i) m
--   cur <- ask
--   if i < cur
--      then return $ parens dm
--      else return $ dm



instance Display Stage where
  display Plus = return $ text "+"
  display Minus = return $ text "-"

instance Display ArgClass where
    display (ArgClassTerm t) = display t
    display (ArgClassPredicate p) = display p
    display (ArgClassLogicalKind l) = display l

instance Display Arg where
    display (ArgTerm t) = display t
    display (ArgPredicate p) = display p
    display (ArgProof p) = display p
    precedence (ArgTerm t) = precedence t
    precedence (ArgProof t) = precedence t
    precedence (ArgPredicate t) = precedence t

    
instance Display ArgName where
    display (ArgNameTerm t) = display t
    display (ArgNamePredicate p) = display p
    display (ArgNameProof l) = display l


instance Display Term where
  display (TermVar n) = return $ text $ name2String n
  
  display (Type i) = return $ text "Type" <+> integer i
  display (Pos _ t) = display t  
  display (Pi binding stage) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        dstage <- display stage
                        return $ text "Pi" <+> (parens (dn <+> colon <+> dstage <+> dty)) <+> text "." <+> dran

  display (TermLambda binding stage) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        dstage <- display stage
                        return $ text "\\" <+> (parens (dn <+> colon <+> dstage <+> dty)) <+> text "." <+> dran

  display (t@(TermApplication t0 arg stage)) = do
    d0 <- dParen (precedence t - 1) t0
    d1 <- dParen (precedence t) arg
    return $ d0 <+> ann stage d1
   where ann Minus = brackets
         ann Plus = id

  display (TermCase1 scrutinee alts) = do
    dScrutinee <- display scrutinee
    dAlts <- mapM dAlt alts
    return $ text "case" <+> dScrutinee <+> text "of" $$
             nest 2 (vcat dAlts)
    where dAlt (con, binding) = do
            lunbind binding $ \(tuples,body) -> 
               let vars = map fst tuples in
               do
                 dcon <- display con
                 dPvars <- mapM (\var -> display var) vars
                 dBody <- display body
                 return $ cat [dcon <+> hsep dPvars <+> text "-> ",nest 2 dBody]
              
  display (w@(Abort t)) = do
    d <- dParen (precedence w) t
    return $ text "abort" <+> d

  display (Rec binding) = do
    lunbind binding $ \((x,f,Embed ty),body) -> do
      df <- display f
      dty <- display ty
      dx <- display x
      dBody <- display body
      return $
         sep [text "rec" <+> dx <+> df <+> text ":" <+> parens dty,
              text ".",
              nest 2 dBody]



  -- display e = error $ "display: " ++ show e

  precedence (TermVar _) = 12
  precedence (Type _) = 12
  precedence (TermApplication _ _ _) = 10
  precedence (Abort _) = 5
  precedence (Pi _ _) = 4
  
  precedence _ = 0
  
instance Display Proof where
  display (ProofVar p) = display p
  display (PosProof _ p) = display p
  display (ProofLambda binding) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        return $ text "\\" <+> (parens (dn <+> colon <+> dty)) <+> text "." <+> dran

  display (p@(ProofApplication p0 arg)) = do
    d0 <- dParen (precedence p - 1) p0
    d1 <- dParen (precedence p) arg
    return $ d0 <+> d1


  display (t@(Join t0 t1)) = do
    d0 <- termParen (precedence t) t0
    d1 <- termParen (precedence t) t1
    return $ text "join" <+> d0 <+> d1

  display (w@(Valax t)) = do
    d <- termParen (precedence w) t
    return $ text "valax" <+> d

  display (t@(Contra t0)) = do
    d0 <- termParen (precedence t) t0
    return $ text "contra" <+> d0


  precedence (ProofVar _) = 12
  precedence (ProofApplication _ _ ) = 10
  precedence (Join _ _ ) = 5
  precedence (Contra _ ) = 5
  precedence (Valax _ ) = 5
  
  precedence _ = 0

instance Display Predicate where
  display (PredicateVar p) = display p
  display (PosPredicate _ p) = display p
  display (PredicateLambda binding) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        return $ text "\\" <+> (parens (dn <+> colon <+> dty)) <+> text "." <+> dran

  display (Forall binding) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        return $ text "Forall" <+> (parens (dn <+> colon <+> dty)) <+> text "." <+> dran

  display (p@(PredicateApplication p0 arg)) = do
    d0 <- dParen (precedence p - 1) p0
    d1 <- dParen (precedence p) arg
    return $ d0 <+> d1

  display (t@(Equal t0 t1)) = do
                     d0 <- dParen (precedence t) t0
                     d1 <- dParen (precedence t) t1
                     return $ fsep [d0, text "=", d1]

  display (w@(Terminate t)) = do
                     dt <- termParen (precedence w) t
                     return $ text "!" <+>  dt
  
  display (t@(Bottom i)) = return $ text "bottom" <+> integer i


  precedence (PredicateVar _) = 12
  precedence (PredicateApplication _ _ ) = 10
  precedence (Equal _ _ ) = 9
  precedence (Terminate _ ) = 7
  
  precedence _ = 0

instance Display LogicalKind where
  display (Formula i) = return $ text "formula" <+> integer i

  display (QuasiForall binding) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        return $ text "Forall" <+> (parens (dn <+> colon <+> dty)) <+> text "." <+> dran

instance Display Declaration where
    display (DeclData d) = display d
    display (DeclPreddecl p) = display p
    display (DeclPreddef p) = display p
    display (DeclProgdef p) = display p
    display (DeclProgdecl p) = display p
    display (DeclProof p) = display p
    display (DeclLogic p) = display p

instance Display Progdef where
  display (Progdef n ty) = do
    dn <- display n
    dty <- display ty
    return $  dn <+> text "::" <+> dty <+> text "."

instance Display Progdecl where
  display (Progdecl n tm) = do
    dn <- display n
    dtm <- display tm
    return $  cat[ dn <+> text ":=", nest 3 $ dtm <> semi] $$ text ""

instance Display Logicdecl where
  display (Logicdecl n ty) = do
    dn <- display n
    dty <- display ty
    return $  dn <+> text "::" <+> dty <> semi
            
instance Display Proofdef where
  display (Proofdef n tm) = do
    dn <- display n
    dtm <- display tm
    return $  cat[ dn <+> text ":=", nest 3 $ dtm <> semi] $$ text ""

instance Display Preddecl where
  display (Preddecl n ty) = do
    dn <- display n
    dty <- display ty
    return $ dn <+> text "::" <+> dty <> semi
            
instance Display Preddef where
  display (Preddef n tm) = do
    dn <- display n
    dtm <- display tm
    return $  cat[ dn <+> text ":=", nest 3 $ dtm <> semi] $$ text ""


instance Display Datatypedecl where
  display (Datatypedecl t1 binding) = do
    lunbind binding $ \(tele,cs) -> do
     d1 <- display t1
     dtele <- displayTele tele
     dcs <- mapM displayCons cs
     return $ hang (text "data" <+> d1 <+> colon <>colon <+> dtele <+> text "where") 2
                       (vcat (punctuate semi dcs)) $$ text "."
    where displayCons (c,t) = do
            dc <- display c
            dt <- display t
            return $ dc <+> colon <+> dt

          displayTele Empty = return $ text "Type"
          displayTele tele = do
             dtele <- display tele
             return $ dtele <+> text ".Type"



instance Display Tele where
    display Empty = return Text.PrettyPrint.empty
    display (TCons binding) = do
      let ((n,stage,Embed ty),tele) = unrebind binding
      dn <- display n
      dty <- display ty
      drest <- display tele
      dst <- display stage
      return $ text "Pi" <+> parens (dn <> colon <> dst <> dty) <> drest












{- Building a small-scale test case for substitution:
 
1. Show: [proof/proofvar]proof is working correctly.

2. Show: [term/termvar]term  is working correctly.

3. Show: [predicate/predicatevar]predicate is working correctly.

4. Show: [arg/argname]proof is working correctly.

5. Show: [term/termvar]predicate is working correctly.

6. Example: [yz/x](\z.zx)
-}

x_term, y_term, z_term, u_term :: Name Term 

x_proof, y_proof, z_proof :: Name Proof 

x_pred, y_pred, z_pred :: Name Predicate

x_term = string2Name "x_term"
y_term = string2Name "y_term"
z_term = string2Name "z_term"
u_term = string2Name "u_term"
x_proof = string2Name "x_proof"
y_proof = string2Name "y_proof"
z_proof = string2Name "z_proof"
x_pred = string2Name "x_pred"
y_pred = string2Name "y_pred"
z_pred = string2Name "z_pred"

--1. Test Case for [proof/proofvar]proof:

-- \z:Z.zx a proof
plzZzx = ProofLambda (bind (ArgNameProof z_proof, (Embed (ArgClassPredicate (PredicateVar z_pred)))) (ProofApplication (ProofVar z_proof) (ArgProof (ProofVar x_proof)))) 

-- yz a proof
pyz = ProofApplication (ProofVar y_proof) (ArgProof (ProofVar z_proof))

-- [yz/x](\z:Z.zx)=\z:Z.z(yz')
test1 = subst x_proof pyz plzZzx

--2. Test Case for [term/termvar]term

--yz is term
tyz = TermApplication (TermVar y_term) (ArgTerm (TermVar z_term)) Plus

-- \z:Y.zx is a term
tlzYzx = TermLambda (bind (ArgNameTerm z_term, (Embed (ArgClassTerm (TermVar y_term)))) (TermApplication (TermVar z_term) (ArgTerm (TermVar x_term)) Plus)) Plus 

-- [yz/x](\z:Z.zx)=\z:Z.z(yz')
test2 = subst x_term tyz tlzYzx

--3. Test Case for [pred/predvar]pred

--yz is pred
pdyz = PredicateApplication (PredicateVar y_pred) (ArgPredicate (PredicateVar z_pred)) 

-- \z:F0.zx is a pred
pdlzF0zx = PredicateLambda (bind (ArgNamePredicate z_pred, (Embed (ArgClassLogicalKind (Formula 0)))) (PredicateApplication (PredicateVar z_pred) (ArgPredicate (PredicateVar x_pred)))) 

--[yz/x]\z:F0.zx=\z:F0.z(yz')
test3 = subst x_pred pdyz pdlzF0zx

--4. Test Case for [arg/argname]proof

--yz is term being promoted to arg 
atyz = ArgTerm (TermApplication (TermVar y_term) (ArgTerm (TermVar z_term)) Plus)

-- \z:U.zx is a proof, but x is termvar
plzUxz = ProofLambda (bind (ArgNameProof z_proof, (Embed (ArgClassPredicate (PredicateVar y_pred)))) (ProofApplication (ProofVar z_proof) (ArgTerm (TermVar x_term)))) 

-- [yz/x](\z:U.zx)=\z:U.z(yz')
test4 = subst (translate x_term) atyz plzUxz

-- 5. Test case for [term/termvar]pred

-- tyz is term


-- \z:Z.zx is a pred, but x is a termvar

pdlzZxz = PredicateLambda (bind (ArgNamePredicate z_pred, (Embed (ArgClassLogicalKind (Formula 0)))) (PredicateApplication (PredicateVar z_pred) (ArgTerm (TermVar x_term)))) 

--[yz/z]\z:U.zx= \z:U.z(yz')
test5 = subst x_term tyz pdlzZxz

