{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

module Language.SepCore.Typecheck where
import Language.SepCore.Syntax
import Data.Maybe
import Unbound.LocallyNameless hiding (Con,isTerm,Val,join,Equal,Refl)
import Unbound.LocallyNameless.Ops(unsafeUnbind)
import qualified Unbound.LocallyNameless.Alpha as Alpha
import qualified Generics.RepLib as RL
import Generics.RepLib hiding (Con,Val,Equal,Refl)
import Text.PrettyPrint
import Data.Typeable
import "mtl" Control.Monad.Reader hiding (join)
import "mtl" Control.Monad.Error hiding (join)
import "mtl" Control.Monad.State hiding (join)
import Control.Exception(Exception)
import Control.Applicative
import Text.Parsec.Pos
import Data.List(nubBy, nub,find, (\\),intersect,sortBy,groupBy)
import qualified Data.Map as M

type TcMonad = FreshMT (ReaderT Context IO)

type Context = M.Map ArgName (Term, Value)
 
lookupVar name context = case (M.lookup name context) of
                          Just a -> Left a
                          Nothing -> Right ("Couldn't find the variable from the current context")

compType :: Term -> Reader Context Term

compType (Type i)  = do return (Type i)

compType (TermVar var) = do   
    theType <- asks (lookupVar (ArgNameTerm var))
    case theType of
      Left a -> return (fst a)
      Right s -> error s
--(bind (argname, Embed (ArgClassTerm t1)) t2)
compType (Pi t stage) = do
  case t of
    bind (argname, Embed (ArgClassTerm t1)) t2 -> theTerm <-compType t1
                                                              case theTerm of
                                                                   Type i -> local (M.insert argname (t1, stage)) ask >> compType t2
                                                                    error "The type of the argument is not well formed."
    _ -> error "unkown"






-- checkData :: Datatypedecl -> IO ()
-- checkData Datatypedecl t1 t2 branches =         checkTerm
