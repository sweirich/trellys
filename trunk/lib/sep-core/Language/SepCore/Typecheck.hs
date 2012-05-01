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

-- global env: Context, having IO side effects.

newtype TCMonad a = TCMonad{ runTCMonad :: ReaderT Context (FreshMT IO) a}   
 deriving (Monad, MonadReader Context, Fresh)


type Context = M.Map ArgName (Term, Value)

lookupVar :: ArgName -> Context -> Either (Term, Value) String
lookupVar name context = case (M.lookup name context) of
                          Just a -> Left a
                          Nothing -> Right ("Can't find variable "++show(name) ++" from the context.")

getTerm :: ArgName -> Context -> Either Term String
getTerm name context = case (lookupVar name context) of
                       Left (t, _) -> Left t 
                       Right s -> Right s

getValue :: ArgName -> Context -> Either Value String
getValue name context = case (lookupVar name context) of
                       Left (_, v) -> Left v 
                       Right s -> Right s

compType :: Term -> TCMonad (Either Term String)

-- | Type Integer
compType (Type i)  =  return (Left (Type i))

-- | TermVar (Name Term)
compType (TermVar var) = asks (getTerm (ArgNameTerm var))

-- | Pi (Bind (ArgName, Embed ArgClassTerm Term) Term) Stage
compType (Pi b stage) = do
                   ((name, Embed (ArgClassTerm t1)), t2) <- unbind b
                   theKind <- compType t1
                   case theKind of
                      Left (Type i) -> local (M.insert name (t1, Value)) (compType t2)
                                        -- FTP(For Test Purpose): return (Right (show t2))
                      Right s -> return (Right s)

-- | TermApplication Term Arg Stage

-- compType (TermApplication t a stage) = do
--                      A <- compType a
--                      b <- compType t
--                     ((name, Embed (ArgClassTerm A), t')) <- unbind b
--                     app b (a, A)




-- test code 
sample = M.fromList [((ArgNameTerm (string2Name "nat")),(Type 0, Value))]

test :: IO()
test = do c <- runFreshMT (runReaderT (runTCMonad (compType (Pi (bind (ArgNameTerm (string2Name "x"), Embed (ArgClassTerm (Type 56))) (TermVar (string2Name "x"))) Plus ))) sample)
          print c

-- checkData :: Datatypedecl -> IO ()
-- checkData Datatypedecl t1 t2 branches =         checkTerm
