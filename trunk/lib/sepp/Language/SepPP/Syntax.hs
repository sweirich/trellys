{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeFamilies  #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-name-shadowing #-}
module Language.SepPP.Syntax (
  Decl(..),Module(..),Expr(..),Tactic(..),
  Stage(..),Kind(..),Alt,
  EName, ModName,
  EExpr(..), EEName,
  down,downAll,
  Tele(..),teleArrow,subTele,teleFromList,fTele,
  isStrictContext, -- var, app
  dynArrow,
  okCtx,
  SynFun(..),
  noTCast,
  tacticPosition, tacticChildren
  ) where

import Unbound.LocallyNameless hiding (Con,Val,Equal,Refl)
import Unbound.LocallyNameless.Alpha(aeqR1)
import Unbound.LocallyNameless.Ops(unsafeUnbind)
import Text.Parsec.Pos
-- import Control.Applicative((<$>), (<*>),Applicative)


import Data.Typeable

-- | 'Unbound' Name representation
type EName = Name Expr

-- Telescopes. Hmmmm.
data Tele = Empty | TCons (Rebind (EName, Stage, Embed Expr, Bool) Tele) deriving (Show)


-- | A module is just a list of definitions.
type ModName = Name Module
data Module = Module ModName [Decl] deriving (Show)

-- Name, type, value
data Decl = ProgDecl EName Expr Expr
          | ProofDecl EName Expr Expr
          | DataDecl Expr (Bind Tele [(EName,Expr)])
          | AxiomDecl EName Expr
          | FlagDecl String Bool
          | OperatorDecl String Int String
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
          | Pi Stage (Bind (EName, Embed Expr, Bool) Expr)  -- Expr
          | Forall (Bind (EName, Embed Expr, Bool) Expr)    -- Predicate

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
          | TCast Expr Expr

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


           -- Existential
          | Exists (Bind (EName,Embed Expr) Expr) -- exists x:T s.t. P(x)
          | EIntro Expr Expr
          | EElim Expr (Bind (EName,EName) Expr)


          -- In a conversion context, the 'Escape' term splices in an equality
          -- proof (or an expression that generates an equality proof).
          | Escape Expr


          | Let Stage (Bind (EName,Maybe EName,Embed Expr) Expr)

          | Aborts Expr


          | WildCard -- For marking arguments that should be inferred.

          | Ann Expr Expr  -- Predicate, Proof, Expr (sort of meta)
          | Pos SourcePos Expr


          | Tactic Tactic
          deriving (Show,Typeable)


data Tactic = Sym Expr
            | Refl
            | Trans Expr Expr 
            | MoreJoin [Expr] 
            | Equiv Integer
            | Injective Expr 
            | Autoconv Expr deriving (Show,Typeable)

tacticPosition :: SourcePos
tacticPosition = newPos "tactic" 0 0

---------------------------------------------------------

type Alt = Bind (String, [(EName,Stage)]) Expr
$(derive_abstract [''SourcePos])
instance Alpha SourcePos

$(derive [''Expr, ''Tactic, ''Module, ''Decl, ''Stage, ''Kind,''Tele])


instance Alpha Expr where
  aeq' _ (Pos _ t1) t2 = t1 `aeq` t2
  aeq' _ t1 (Pos _ t2) = t1 `aeq` t2
  aeq' _ (TCast t1 _) t2 = t1 `aeq` t2
  aeq' _ t1 (TCast t2 _) = t1 `aeq` t2
  aeq' c t1 t2 = aeqR1 rep1 c t1 t2

instance Alpha Module
instance Alpha Decl
instance Alpha Stage
instance Alpha Kind
instance Alpha Tele
instance Alpha Tactic

instance Subst Expr Expr where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Expr Stage
instance Subst Expr Kind
instance Subst Expr SourcePos
instance Subst Expr Tele
instance Subst Expr Tactic

-- | isStrictContext finds a term in a strict context.  If it finds
-- one, it returns the term, along with the continuation of the term.
isStrictContext :: Expr -> Maybe (Expr, Expr -> Expr)
isStrictContext (Pos _ t) = isStrictContext t
isStrictContext (Escape e) = Just (e,id)
isStrictContext (App e1 stage e2) =
 case isStrictContext e1 of
   Just (e,k1) -> Just (e,\v -> App (k1 v) stage e2)
   Nothing ->  case isStrictContext e2 of
                 Just (e,k2) -> Just (e,\v -> App e1 stage (k2 v))
                 Nothing -> Nothing
isStrictContext (Case e term bs) =  
      case isStrictContext e of
        Just (e',k) -> Just (e',\v -> Case (k v) term bs)
        Nothing -> Nothing

isStrictContext _ = Nothing


-- | down removes position information from the top level of an Expr.
down :: Expr -> Expr
down (Pos _ t) = down t
down t = t

-- | downAll removes position information everywhere in an Expr
downAll :: Rep a => a -> a
downAll t = everywhere (mkT down) t




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
           | ETCast EExpr
           | EPi Stage (Bind (EEName, Embed EExpr) EExpr)
  deriving (Show)


$(derive [''EExpr])

instance Alpha EExpr where
  aeq' _ (ETCast t1) t2 = t1 `aeq` t2
  aeq' _ t1 (ETCast t2) = t1 `aeq` t2
  aeq' c t1 t2 = aeqR1 rep1 c t1 t2

instance Subst EExpr EExpr where
  isvar (EVar x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst EExpr Stage where
  isvar _ = Nothing

teleArrow :: Tele -> Expr -> Expr
teleArrow Empty end = end
teleArrow (TCons binding) end = Pi stage (bind (n,ty,inferred) arrRest)
 where ((n,stage,ty,inferred),rest) = unrebind binding
       arrRest = teleArrow rest end




-- | Remove all tcasts from a term.
noTCast :: Rep a => a -> a
noTCast t = everywhere (mkT f) t
  where f (ETCast t) = t
        f t' = t'





-- Convert an arrow to be all dynamic.
dynArrow :: Expr -> Expr
dynArrow (Pi _ binding) = Pi Dynamic (bind (n,ty,False) rest)
  where ((n,ty,_),body) = unsafeUnbind binding
        rest = dynArrow body
dynArrow t  = t

-- Given a telescope, a list of expressions to substitute for the
-- telescope, and a subject, perform substitution
subTele :: Tele -> [Expr] -> Expr -> Expr
subTele Empty [] x = x
subTele (TCons binding) (ty:tys) x = subst n ty $ subTele rest tys x
  where ((n,_,_,_),rest) = unrebind binding
subTele _ _ _ =
  error "Can't construct a telescope substitution, arg lengths don't match"

-- FIXME: Add in the inferred argument
teleFromList :: [(Stage, (Bool, EName, Expr))] -> Tele
teleFromList args =
  foldr (\(st,(inf,n,ty)) r -> TCons (rebind (n,st,Embed ty, inf) r))
        Empty args

-- | fTele is a foldr over telescopes.
fTele :: ((EName, Stage, Embed Expr, Bool) -> t -> t) -> t -> Tele -> t
fTele f i (TCons rebinding) = f pat (fTele f i rest)
  where (pat,rest) = unrebind rebinding
fTele _ i Empty = i


-- Check to see if an escaped explicit equality appears outside an erased
-- position. Returns True if the context is okay, false otherwise.
okCtx :: Expr -> Bool
okCtx (Pos _ t) = okCtx t
okCtx (Escape t) = case down t of
                     (Equal _ _) -> False
                     _ -> True
okCtx (App t Static  _) = okCtx t
okCtx expr = and $ map okCtx $ children expr

-- | Get all of the immediate subexpressions of an expression.
children :: Expr -> [Expr]
children (Pi _ binding) = [ty,body]
  where ((_,Embed ty,_),body) = unsafeUnbind binding
children (Forall binding) = [ty,body]
  where ((_,Embed ty,_),body) = unsafeUnbind binding
children (App t1 _ t2) = [t1,t2]
children (Lambda _ _  binding) = [ty,body]
  where ((_,Embed ty),body) = unsafeUnbind binding
children (Case s q binding) = cons q $ [s] ++ arms
  where (_,alts) = unsafeUnbind binding
        arms = [bdy | a <- alts, ((_,_),bdy) <- [unsafeUnbind a]]
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
children (Let _ binding) = [t,body]
  where ((_,_,Embed t),body) = unsafeUnbind binding
children (Aborts x) = [x]
children (Ann x y) = [x,y]
children (Pos _ e) = children e
children (Exists binding) = [ty,body]
  where ((_,Embed ty),body) = unsafeUnbind binding
children (EIntro e1 e2) = [e1,e2]
children (EElim expr binding) = [expr,body]
  where (_,body) = unsafeUnbind binding
children (Tactic t) = tacticChildren t          

children _ = []

-- | Get the children of tactics.
tacticChildren :: Tactic -> [Expr]
tacticChildren (Sym x) = [x]
tacticChildren (Trans x y) = [x,y]
tacticChildren (MoreJoin es) = es
tacticChildren Refl = []
tacticChildren (Equiv _) = []
tacticChildren (Autoconv t) = [t]
tacticChildren (Injective t) = [t]


childrenTele :: Tele -> [Expr]
childrenTele Empty = []
childrenTele (TCons rebinding) = e:(childrenTele rest)
  where ((_,_,Embed e,_),rest) = unrebind rebinding




class SynFun e where
  type LamArg e
  type PiArg e
  type AppArg e

  unrollLam :: Fresh m => e -> m ([LamArg e], e)
  rollLam :: [LamArg e] -> e -> e

  unrollPi :: Fresh m => e -> m ([PiArg e], e)
  rollPi :: [PiArg e] -> e -> e

  unrollApp :: e -> (e,[AppArg e])
  rollApp :: e -> [AppArg e] -> e


instance SynFun Expr where
  type LamArg Expr = (EName,Kind,Stage,Expr)
  type PiArg Expr = (EName,Stage,Expr,Bool)
  type AppArg Expr = (Expr,Stage)

  unrollLam (Pos _ t) = unrollLam t
  unrollLam (Lambda kind stage binding) = do
    ((nm,Embed ty),body) <- unbind binding
    (rest,range) <- unrollLam body
    return ((nm,kind,stage,ty):rest,range)
  unrollLam t = return ([],t)

  rollLam args ran = foldr lam ran args
    where lam (arg,kind,stage,ty) body = Lambda kind stage (bind (arg,Embed ty) body)

  unrollPi (Pos _ t) = unrollPi t
  unrollPi (Pi stage binding) = do
    ((nm,Embed ty,inferred),body) <- unbind binding
    (rest,range) <- unrollPi body
    return ((nm,stage,ty,inferred):rest,range)
  unrollPi t = return ([],t)

  rollPi args ran = foldr pi ran args
    where pi (arg,stage,ty,inf) body = Pi stage (bind (arg,Embed ty,inf) body)

  unrollApp t = go t []
    where go (Pos _ t) accum = go t accum
          go (App t1 stage t2) accum = go t1 ((t2,stage):accum)
          go t' accum = (t',accum)


  rollApp f args = foldl app f args
    where app f' (arg,stage) = App f' stage arg


instance SynFun EExpr where
  type LamArg EExpr = EEName
  type PiArg EExpr = (EEName,EExpr,Stage)
  type AppArg EExpr = EExpr

  unrollLam (ELambda binding) = do
    (arg,t) <- unbind binding
    (args,body) <- unrollLam t
    return (arg:args,body)

  unrollLam (ERec binding) = do
    ((_,args),rest) <- unbind binding
    (args',body) <- unrollLam rest
    return (args ++ args', body)
  unrollLam t = return ([],t)

  rollLam [] t = t
  rollLam (n:ns) t = ELambda (bind n (rollLam ns t))


  unrollPi (EPi stage binding) = do
    ((arg,Embed ty),rest) <- unbind binding
    (args,body) <- unrollPi rest
    return ((arg,ty,stage):args,body)
  unrollPi t = return ([],t)

  rollPi [] t = t
  rollPi ((n,ty,stage):args) t = EPi stage (bind (n,Embed ty) (rollPi args t))

  unrollApp t = go t []
    where go (EApp t1 t2) accum = go t1 (t2:accum)
          go t' accum = (t',accum)

  rollApp t args = foldl EApp t args
