module Language.SepCore.TypeCheck where

import Language.SepCore.Syntax

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


typecheck :: Module -> IO (Either TypeError ())
typecheck mod = do
  runErrorT $ runFreshMT $ runReaderT (evalStateT (runTCMonad (typecheckModule mod)) flagMap) emptyEnv
