{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

module Language.SepCore.Typecheck2 where
import Prelude hiding (pred,compare)
import Language.SepCore.Syntax
import Language.SepCore.PrettyPrint
import Language.SepCore.Parser(getPosition)
import Language.SepCore.Lexer
import Data.Maybe
import Unbound.LocallyNameless hiding (Con,isTerm,Val,join,Equal,Refl, flatten)
import Unbound.LocallyNameless.Ops(unsafeUnbind)
import qualified Unbound.LocallyNameless.Alpha as Alpha
import qualified Generics.RepLib as RL hiding (flatten)
import Generics.RepLib hiding (Con,Val,Equal,Refl, flatten)
import Text.PrettyPrint
import Data.Typeable
import Data.Functor.Identity
import "mtl" Control.Monad.Reader hiding (join)
import "mtl" Control.Monad.Error hiding (join)
import "mtl" Control.Monad.State hiding (join)
import Control.Exception(Exception)
import Control.Applicative
import Data.List(nubBy, nub,find, (\\),intersect,sortBy,groupBy)
import qualified Data.Map as M
import Unbound.LocallyNameless.Ops(unsafeUnbind)
import Data.Set
-- global env: Context, having IO side effects.

newtype TCMonad a = TCMonad{runTCMonad ::  ReaderT Context (FreshMT (ErrorT Doc Identity)) a}   
 deriving (Monad, MonadReader Context, Fresh, MonadError Doc)

type Context = M.Map ArgName (ArgClass, Value)

type Env = StateT Context (FreshMT IO)

type LocalEnv = StateT Context (FreshMT Identity)

instance Disp Context where
  disp context = (vcat [ disp argname<>colon <+> disp argclass | (argname, (argclass,_)) <-(M.toList context)])

instance Error Doc where
    strMsg s = text s
    noMsg = strMsg "<unknown>"

lookupVar ::  ArgName  ->  TCMonad(ArgClass, Value) 
lookupVar name = do
  context <- ask
  case (M.lookup name context) of
    Just a -> return a
    Nothing -> throwError $ (disp "Can't find variable ") <+> (disp name) <+> (disp "from the context.")

getClass :: ArgName  -> TCMonad ArgClass
getClass name  = do
   (argclass, _) <- (lookupVar name) `catchError` (\ e -> throwError $ e <+> (disp "in the use of getClass"))
   return argclass

getValue :: ArgName  -> TCMonad Value
getValue name  = do
   (_, v) <- (lookupVar name) `catchError` (\ e -> throwError $ e <+> (disp "in the use of getValue"))
   return v

-- \Gamma |- LK : Logical i

compSK :: LogicalKind -> TCMonad SuperKind

-- | LK_Formula
compSK (Formula i) = return (Logical (i+1))

-- | LK_Predicate
compSK (QuasiForall b) = do ((name, Embed a), lk) <- unbind b
                            case a of
                              ArgClassTerm t -> do
                                     (Type i) <- (compType t) >>= ensureType 
                                     (Logical j) <- local (M.insert name (ArgClassTerm t, NonValue)) (compSK lk)
                                     return  (Logical (max (i+1) j))
                              ArgClassPredicate p -> do
                                     (Formula i) <- compLK p >>= ensureFormula
                                     (Logical j) <- local (M.insert name (ArgClassPredicate p, NonValue)) (compSK lk)
                                     return  (Logical (max (i+1) j))
                              _ -> throwError $ disp "unsupport argClass for " <+> disp (QuasiForall b)

compSK (PosLK p lk) = compSK lk `catchError` (\ e -> throwError $ disp p <+> e)

compLK :: Predicate -> TCMonad LogicalKind 

compLK (PosPredicate p pred) = compLK pred `catchError` (\ e -> throwError $ disp p <+> e)

-- | Predicate_Var, this function may produce position info
compLK (PredicateVar p) = do 
  theKind <- (getClass (ArgNamePredicate p)) >>= ensureArgClassLK
  compSK theKind
  return theKind

-- | Predicate_Bottom
compLK (Bottom i) = return (Formula i)

-- | Predicate_Terminates
compLK (Terminate t) = do compType t
                          return (Formula 0)

-- | Predicate_k_EQ
compLK (Equal t1 t2) = do compType t1
                          compType t2
                          return (Formula 0)

-- | Predicate_forall 1,2,3,4
compLK (Forall b) = do 
  ((argname, Embed argclass),pred) <- unbind b
  case argclass of
    ArgClassPredicate p -> do 
      (Logical i) <- compLK p >>= compSK 
      (Formula j)  <- ensureFormula =<< (local (M.insert argname (ArgClassPredicate p, NonValue)) (compLK pred)) 
      return  (Formula (max i j))
    ArgClassTerm t -> do 
      (Type i) <- compType t >>= ensureType
      (Formula j) <- local (M.insert argname (ArgClassTerm t, NonValue)) (compLK pred) >>= ensureFormula
      if i==0 then return (Formula (max j 1)) else return (Formula (max j i))
    ArgClassLogicalKind lk -> do 
      (Logical i) <- compSK lk
      (Formula j) <- local (M.insert argname (ArgClassLogicalKind lk, NonValue)) (compLK pred) >>= ensureFormula
      return  (Formula (max i j))

-- | Predicate_Lam
compLK (PredicateLambda b) = do 
  ((argname, Embed argclass),pred) <- unbind b
  case argclass of
    ArgClassPredicate p -> do 
      compLK p
      theKind <- local (M.insert argname (ArgClassPredicate p, NonValue)) (compLK pred)
      return (QuasiForall (bind (argname, Embed (ArgClassPredicate p)) theKind))
    ArgClassTerm t -> do 
      compType t >>= ensureType
      theKind <- local (M.insert argname (ArgClassTerm t, NonValue)) (compLK pred)
      return (QuasiForall (bind (argname, Embed (ArgClassTerm t)) theKind))     
    ArgClassLogicalKind lk -> do 
       compSK lk
       theKind <- local (M.insert argname (ArgClassLogicalKind lk, NonValue)) (compLK pred)
       return (QuasiForall (bind (argname, Embed (ArgClassLogicalKind lk)) theKind))
    
-- | Predicate_app
compLK (PredicateApplication p a) = do 
  (QuasiForall b) <- compLK p >>= ensureQForall 
  ((argname, Embed argclass),lk) <- unbind b 
  case argname of
    ArgNameTerm at -> do
        t <- ensureArgTerm a 
        theType <- compType t
        if aeq argclass (ArgClassTerm theType) then return (subst at t lk) else throwError $ disp ("Expected type: ") <+>disp(argclass) <+> disp(" Actual type:")<+> disp(ArgClassTerm theType) 
    ArgNamePredicate pt -> do
        pred <- ensureArgPredicate a 
        theKind <- compLK pred
        if aeq argclass (ArgClassLogicalKind theKind) then return (subst pt pred lk) else throwError $ disp ("Expected logical kind:")<+> disp(argclass) <+> disp ("Actual kind:")<+> disp(ArgClassLogicalKind theKind)
    ArgNameProof prt-> do
        pr <- ensureArgProof a
        theP <- compPred pr
        if aeq argclass (ArgClassPredicate theP) then return (subst prt pr lk) else throwError $ disp ("Expected Predicate:")<+>disp(argclass) <+> disp ("Actual predicate:")<+> disp (ArgClassPredicate theP) 
        





compPred = undefined
--compLK = undefined
compType = undefined

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
                 _ -> throwError $ vcat [disp ("Expected:") <+> disp "Type", disp ("Actually get:")<+> disp t ]
                                  
ensureFormula t = case unWrapLKPos t of 
                    (Formula i) -> return (Formula i)
                    _ -> throwError $ vcat [disp ("Expected:") <+> disp "Formula", disp ("Actually get:")<+> disp t ]

ensureQForall t = case unWrapLKPos t of 
                    (QuasiForall b) -> return (QuasiForall b)
                    _ -> throwError $  disp ("Unexpected:")<+> disp t 

ensureArgClassLK (ArgClassLogicalKind lk) = return lk
ensureArgClassLK t = throwError $  vcat [disp ("Expected:") <+> disp "any LogicalKind", disp ("Actually get:")<+> disp t ]

ensureArgTerm (ArgTerm t) = return t                                              
ensureArgTerm t = throwError $  disp ("Unexpected:")<+> disp t 

ensureArgPredicate (ArgPredicate t) = return t                                              
ensureArgPredicate t = throwError $  disp ("Unexpected:")<+> disp t 

ensureArgProof (ArgProof t) = return t                                              
ensureArgProof t = throwError $  disp ("Unexpected:")<+> disp t 
