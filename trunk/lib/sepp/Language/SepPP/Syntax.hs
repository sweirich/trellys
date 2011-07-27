{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances  #-}
module Language.SepPP.Syntax (
  Decl(..),Module(..),Expr(..),
  Stage(..),Kind(..),Alt,
  EName, ModName,
  EExpr(..), EEName,
  down,downAll,
  Tele(..),teleArrow,subTele,teleFromList,
  splitApp, splitApp', isStrictContext, var, app,
  okCtx) where

import Unbound.LocallyNameless hiding (Con,Val)
import Unbound.LocallyNameless.Alpha(aeqR1)
import Unbound.LocallyNameless.Ops(unsafeUnbind)
import Text.Parsec.Pos
import Control.Monad(mplus)
import Control.Applicative((<$>), (<*>),Applicative)


import Data.Typeable

-- | 'Unbound' Name representation
type EName = Name Expr

-- Telescopes. Hmmmm.
data Tele = Empty | TCons (Rebind (EName, Stage, Embed Expr) Tele) deriving (Show)



-- | A module is just a list of definitions.
type ModName = Name Module
data Module = Module ModName [Decl] deriving (Show)

-- Name, type, value
data Decl =  ProgDecl EName Expr Expr
          |  ProofDecl EName Expr Expr
          | DataDecl Expr (Bind Tele [(EName,Expr)])
          | AxiomDecl EName Expr
          | FlagDecl String Bool
     deriving Show

data Stage = Dynamic | Static deriving Eq

instance Show Stage where
  show Static = "static"
  show Dynamic = "runtime"

data Kind = Form | Program deriving (Eq,Show)
-- | The representation of SepPP expressions.

data Expr = Var EName                                 -- Expr, Proof
          | Con EName                                 -- Expr
          | Formula Integer                           -- LogicalKind
          | Type                                      -- Expr
            -- |
          | Pi Stage (Bind (EName, Embed Expr) Expr)  -- Expr
          | Forall (Bind (EName, Embed Expr) Expr)    -- Predicate

            -- We keep a stage annotation around so that we can erase an
            -- application without knowing its type.
          | App Expr Stage Expr                       -- Predicate, Proof, Expr
          | Lambda Kind Stage (Bind (EName, Embed Expr) Expr)  -- Predicate, Proof, Expr

            -- There are actually two types of case expressions in the design
            -- document. We combine these two, with the extra termination proof
            -- argument wrapped in Maybe.

          | Case Expr (Maybe Expr) (Bind EName [Alt])       -- Proof, Expr


          | TerminationCase Expr (Bind EName (Expr,Expr))    -- Proof


          | Join Integer Integer                      -- Proof
                                                      -- intros a
          | Equal Expr Expr                           -- Predicate

          | Val Expr                                  -- Proof
                                                      -- intros a
          | Terminates Expr                           -- Predicate

          -- Contra is used when you have an equation between
          -- distinct constructors.
          | Contra Expr                               -- Proof
          -- Contraabort is used when you have an proof that t = abort
          -- and a proof that t terminates.
          | ContraAbort Expr Expr                     -- Proof

          -- The term argument is the type you wish to ascribe
          | Abort Expr                                -- Expr
          | Show Expr                                 -- Expr


          -- The bool associated with the equality proof is whether or not the
          -- type occurs in an erased position. If it does, then the term should
          -- be an equality proof. If it doesn't then the term should be some
          -- value with the a type that is an equality proof.
          | Conv Expr [Expr] (Bind [EName] Expr)  -- Proof, Expr
          | ConvCtx Expr Expr -- Simple quote style contexts


          -- For inductive proofs we have an ordering. The argument is the
          -- witness to the equality that demonstrates the equality.
          | Ord Expr                                  -- Proof
                                                      -- intros a
          | IndLT Expr Expr                           -- Pred


          | OrdTrans Expr Expr


          | Ind (Bind (EName, Tele, EName) Expr) -- proof
          | Rec (Bind (EName,Tele) Expr) -- term

          -- In a conversion context, the 'Escape' term splices in an equality
          -- proof (or an expression that generates an equality proof).
          | Escape Expr

          | Let (Bind (EName,EName,Embed Expr) Expr)

          | Aborts Expr
          | Sym Expr -- Should be a derived form
          | Refl -- Should be a derived form
          | Trans Expr Expr -- Should be a derived form
          | MoreJoin [Expr] -- Should be a derived form

          | Ann Expr Expr  -- Predicate, Proof, Expr (sort of meta)
          | Pos SourcePos Expr
          deriving (Show,Typeable)


---------------------------------------------------------

type Alt = Bind (String, [EName]) Expr
$(derive_abstract [''SourcePos])
instance Alpha SourcePos

$(derive [''Expr, ''Module, ''Decl, ''Stage, ''Kind,''Tele])


instance Alpha Expr where
  aeq' c (Pos _ t1) t2 = t1 `aeq` t2
  aeq' c t1 (Pos _ t2) = t1 `aeq` t2
  aeq' c t1 t2 = aeqR1 rep1 c t1 t2

instance Alpha Module
instance Alpha Decl
instance Alpha Stage
instance Alpha Kind
instance Alpha Tele

instance Subst Expr Expr where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Expr Stage
instance Subst Expr Kind
instance Subst Expr SourcePos
instance Subst Expr Tele



splitApp (App t0 _ t1) = splitApp' t0 [t1]
  where splitApp' (App s0 _ s1) acc = splitApp' s0 (s1:acc)
        splitApp' (Pos _ t) acc = splitApp' t acc
        splitApp' s acc = s:acc
splitApp (Pos _ t) = splitApp t
splitApp t = []


splitApp' t = case splitApp t of
                [] -> (t,[])
                (x:xs) -> (x,xs)

isStrictContext (Pos _ t) = isStrictContext t
isStrictContext (Escape e) = Just (e,id)
isStrictContext (App e1 stage e2) =
 case isStrictContext e1 of
   Just (e,k1) -> Just (e,\v -> App (k1 v) stage e2)
   Nothing ->  case isStrictContext e2 of
                 Just (e,k2) -> Just (e,\v -> App e1 stage (k2 v))
                 Nothing -> Nothing


isStrictContext (Case e term bs) = case isStrictContext e of
                               Just (e',k) -> Just (e',\v -> Case (k v) term bs)


isStrictContext _ = Nothing

var s = Var (string2Name s)
app f x = App f Dynamic x



down (Pos _ t) = down t
down t = t

-- downAll :: Expr -> TCMonad Expr
downAll t = everywhere (mkT f') t
  where f' (Pos _ t) = t
        f' t = t




-- | Erased Terms
type EEName = Name EExpr
data EExpr = EVar EEName
           | ECon EEName
           | EApp EExpr EExpr
           | ELambda (Bind EEName EExpr)
           | ERec (Bind (EEName, [EEName]) EExpr)
           | ECase EExpr [Bind (String,[EEName]) EExpr]
           | ELet (Bind (EEName, Embed EExpr) EExpr)
           | EType
           | EAbort
           | EPi Stage (Bind (EEName, Embed EExpr) EExpr)
  deriving (Show)


-- cValOfApp :: EExpr -> Bool
-- cValOfApp (EApp f x) = cValOfApp f && erasedValue x
-- cValOfApp (ECon _)   = True
-- cValOfApp _         = False

-- erasedValue :: EExpr -> Bool
-- erasedValue (ECase _ _) = False
-- erasedValue e@(EApp _ _) = cValOfApp e
-- erasedValue (ELet _) = False
-- erasedValue (EVar _) = False
-- erasedValue _ = True




$(derive [''EExpr])

instance Alpha EExpr
instance Subst EExpr EExpr where
  isvar (EVar x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst EExpr Stage where
  isvar _ = Nothing

teleArrow Empty end = end
teleArrow (TCons binding) end = Pi stage (bind (n,ty) arrRest)
 where ((n,stage,ty),rest) = unrebind binding
       arrRest = teleArrow rest end


-- StaticTele


subTele :: Tele -> [Expr] -> Expr -> Expr
subTele Empty [] x = x
subTele (TCons binding) (ty:tys) x = subst n ty $ subTele rest tys x
  where ((n,_,_),rest) = unrebind binding
subTele _ _ _ =
  error "Can't construct a telescope substitution, arg lengths don't match"


teleFromList args = foldr (\(st,(n,ty)) r -> TCons (rebind (n,st,Embed ty) r))
                    Empty args





-- Check to see if an escaped explicit equality appears outside an erased
-- position. Returns True if the context is okay, false otherwise.


okCtx (Pos _ t) = okCtx t
okCtx (Escape t) = case down t of
                     (Equal _ _) -> False
                     _ -> True
okCtx (App t Static  _) = okCtx t
okCtx expr = and $ map okCtx $ children expr

-- FIXME: Replace with RepLib...
children (Pi _ binding) = [ty,body]
  where ((n,Embed ty),body) = unsafeUnbind binding
children (Forall binding) = [ty,body]
  where ((n,Embed ty),body) = unsafeUnbind binding
children (App t1 _ t2) = [t1,t2]
children (Lambda _ _  binding) = [ty,body]
  where ((n,Embed ty),body) = unsafeUnbind binding

children (Case e q binding) = cons q $ [e] ++ arms
  where (n,alts) = unsafeUnbind binding
        arms = [bdy | a <- alts, ((n,_),bdy) <- [unsafeUnbind a]]
        cons (Just e) es = e:es
        cons Nothing es = es

children (TerminationCase e binding) = [e,a,t]
 where (_,(a,t)) = unsafeUnbind binding
children (Equal x y) = [x,y]
children (Val x) = [x]
children (Terminates x) = [x]
children (Contra x) = [x]
children (ContraAbort x y) = [x,y]
children (Abort x) = [x]
children (ConvCtx x y) = [x,y]
children (Ord x) = [x]
children (IndLT x y) = [x,y]
children (OrdTrans x y) = [x,y]
children (Ind binding) = body:(childrenTele tele)
  where ((_,tele,_),body) = unsafeUnbind binding
children (Rec binding) = body:(childrenTele tele)
  where ((_,tele),body) = unsafeUnbind binding

children (Escape x) = [x]
children (Let binding) = [t,body]
  where ((_,_,Embed t),body) = unsafeUnbind binding
children (Aborts x) = [x]
children (Sym x) = [x]
children (Trans x y) = [x,y]
children (MoreJoin es) = es
children (Ann x y) = [x,y]
children (Pos _ e) = children e
children _ = []

childrenTele Empty = []
childrenTele (TCons rebinding) = e:(childrenTele rest)
  where ((_,_,Embed e),rest) = unrebind rebinding
