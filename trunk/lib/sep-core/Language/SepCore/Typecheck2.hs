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

newtype TCMonad a = TCMonad{runTCMonad ::  ReaderT Context (FreshMT Identity) a }   
 deriving (Monad, MonadReader Context, Fresh)
type Context = M.Map ArgName (ArgClass, Value)
type Env = StateT Context (FreshMT IO)
type LocalEnv = StateT Context (FreshMT Identity)

instance Disp Context where
  disp context = (vcat [ disp argname<>colon <+> disp argclass | (argname, (argclass,_)) <-(M.toList context)])
instance Error Doc where
    strMsg doc = disp doc 

lookupVar :: MonadError Doc  m => ArgName -> Context ->  m(ArgClass, Value) 
lookupVar name context = case (M.lookup name context) of
                          Just a -> return a
                          Nothing -> throwError $ strMsg $ "Can't find variable "++show(name) ++" from the context."

-- getClass :: ArgName -> Context -> Either ArgClass String
-- getClass name context = case (lookupVar name context) of
--                        Left (t, _) -> Left t 
--                        Right s -> Right $ s++"getClass"

-- getValue :: ArgName -> Context -> Either Value String
-- getValue name context = case (lookupVar name context) of
--                        Left (_, v) -> Left v 
--                        Right s -> Right s

