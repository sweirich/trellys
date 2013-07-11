{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

module Language.SepCore.Monad where
import Language.SepCore.Syntax
import Language.SepCore.Error
import Language.SepCore.PrettyPrint
import qualified Data.Map as M
import "mtl" Control.Monad.Reader hiding (join)
import "mtl" Control.Monad.Error hiding (join)
import "mtl" Control.Monad.State hiding (join)
import Control.Exception(Exception)
import Control.Applicative
import Data.Functor.Identity
import Text.PrettyPrint
import Unbound.LocallyNameless hiding (Con,isTerm,Val,join,Equal,Refl, flatten)
import Unbound.LocallyNameless.Ops(unsafeUnbind)
import qualified Unbound.LocallyNameless.Alpha as Alpha
import qualified Generics.RepLib as RL hiding (flatten)
import Generics.RepLib hiding (Con,Val,Equal,Refl, flatten)



newtype TCMonad a = TCMonad{runTCMonad :: (ReaderT CombineContext (FreshMT (ErrorT TypeError Identity)))  a}   
 deriving (Monad, MonadReader CombineContext,Fresh, MonadError TypeError, Applicative, Functor)

type CombineContext = (Context, DefContext)

type Context = M.Map ArgName (ArgClass, Value)

type DefContext = M.Map ArgName Arg

type Env = StateT CombineContext (FreshMT (ErrorT TypeError IO))

instance Disp Context where
  disp context = hang (text "Current context:") 2 (vcat [ disp argname<>colon<>colon <+> disp argclass | (argname, (argclass,_)) <-(M.toList context)])

instance Disp DefContext where
  disp context = hang (text "Current definitions:") 2 (vcat [ disp argname<>colon<>text "=" <+> disp arg | (argname, arg) <-(M.toList context)])

lookupVar ::  ArgName  ->  TCMonad(ArgClass, Value) 
lookupVar name = do
  context <- ask
  case (M.lookup name (fst context)) of
    Just a -> return a
    Nothing -> typeError $ (disp "Can't find variable ") <+> (disp name) <+> (disp "from the context.")

mapFst :: (a -> a) -> (a,b) -> (a, b)
mapFst f (a,b) = (f a, b)

mapSnd :: (b -> b) -> (a,b) -> (a, b)
mapSnd f (a,b) = (a, f b)

--withVar :: ArgName -> Type -> Value -> TCMonad a -> TCMonad a

withVar x (ty, val) = local (mapFst(M.insert x (ty, val)))



getClass :: ArgName  -> TCMonad ArgClass
getClass name  = do
   (argclass, _) <- (lookupVar name) 
   return argclass

getValue :: ArgName  -> TCMonad Value
getValue name  = do
   (_, v) <- (lookupVar name) 
   return v
-- unWrap the outermost Pos in term.
unWrapTermPos (Pos _ t) = unWrapTermPos t
unWrapTermPos t = t

unWrapProofPos (PosProof _ t) = unWrapProofPos t
unWrapProofPos t = t

unWrapPredicatePos (PosPredicate _ t) = unWrapPredicatePos t
unWrapPredicatePos t = t

unWrapLKPos (PosLK _ t) = unWrapLKPos t
unWrapLKPos t = t

ensureType t = case unWrapTermPos t of
                 Type i -> return (Type i)
                 _ -> typeError $ vcat [disp ("Expected:") <+> disp "Type", disp ("Actually get:")<+> disp t ]
                                  
ensureFormula t = case unWrapLKPos t of 
                    (Formula i) -> return (Formula i)
                    _ -> typeError $ vcat [disp ("Expected:") <+> disp "Formula", disp ("Actually get:")<+> disp t ]

ensureQForall t = case unWrapLKPos t of 
                    (QuasiForall b) -> return (QuasiForall b)
                    _ -> typeError $  disp ("Unexpected:")<+> disp t 

ensureForall t = case unWrapPredicatePos t of 
                    (Forall b) -> return (Forall b)
                    _ -> typeError $  disp ("Unexpected:")<+> disp t 

ensurePi t = case unWrapTermPos t of 
                    (Pi b st) -> return (Pi b st)
                    _ -> typeError $  disp ("Unexpected:")<+> disp t 

ensureEqual p = case unWrapPredicatePos p of
                 Equal t1 t2 -> return (Equal t1 t2)
                 _ -> typeError $ vcat [disp ("Expected:") <+> disp "t = t'", disp ("Actually get:")<+> disp p ]

ensureArgClassLK (ArgClassLogicalKind lk) = return lk
ensureArgClassLK t = typeError $  vcat [disp ("Expected:") <+> disp "any LogicalKind", disp ("Actually get:")<+> disp t ]

ensureArgClassPred (ArgClassPredicate pred) = return pred
ensureArgClassPred t = typeError $  vcat [disp ("Expected:") <+> disp "any Predicate", disp ("Actually get:")<+> disp t ]

ensureArgClassTerm (ArgClassTerm t) = return t
ensureArgClassTerm t = typeError $  vcat [disp ("Expected:") <+> disp "any Term", disp ("Actually get:")<+> disp t ]


ensureArgTerm (ArgTerm t) = return t                                              
ensureArgTerm t = typeError $  disp ("Unexpected:")<+> disp t 

ensureArgPredicate (ArgPredicate t) = return t                                              
ensureArgPredicate t = typeError $  disp ("Unexpected:")<+> disp t 

ensureArgProof (ArgProof t) = return t                                              
ensureArgProof t = typeError $  disp ("Unexpected:")<+> disp t 
