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


type Context = M.Map ArgName (ArgClass, Value)

lookupVar :: ArgName -> Context -> Either (ArgClass, Value) String
lookupVar name context = case (M.lookup name context) of
                          Just a -> Left a
                          Nothing -> Right ("Can't find variable "++show(name) ++" from the context.")

getClass :: ArgName -> Context -> Either ArgClass String
getClass name context = case (lookupVar name context) of
                       Left (t, _) -> Left t 
                       Right s -> Right s

getValue :: ArgName -> Context -> Either Value String
getValue name context = case (lookupVar name context) of
                       Left (_, v) -> Left v 
                       Right s -> Right s

-- \Gamma |- LK : Logical i

compSK :: LogicalKind -> TCMonad (Either SuperKind String)

-- | LK_Formula
compSK (Formula i) = return (Left (Logical i+1))

-- | LK_Predicate
compSK (QuasiForall b) = do ((name, Embed a), lk) <- unbind b
                            case a of
                              ArgClassTerm t -> 
                                do theType <-compType t
                                   case theType of 
                                     Left (Type i) -> do
                                                  c <- local (M.insert name (ArgClassTerm t, NonValue)) (compSK lk)
                                                  case c of
                                                    Left (Logical j) -> return (Left (Logical (max i+1 j)))
                                                    Left _ -> return (Right "undefined")
                                                    Right s -> return (Right s)
                                     Left _ -> return (Right "undefined")
                                     Right s -> return (Right s)
                              ArgClassPredicate p -> 
                                do theKind <- compLK p
                                   case theKind of 
                                     Left (Formula i) -> do
                                                  c <- local (M.insert name (ArgClassPredicate p, NonValue)) (compSK lk)
                                                  case c of
                                                    Left (Logical j) -> return (Left (Logical (max i+1 j)))
                                                    Left _ -> return (Right "undefined")
                                                    Right s -> return (Right s)
                                     Left _ -> return (Right "undefined")
                                     Right s -> return (Right s)
                              _ -> return (Right "undefined")


compLK :: Predicate -> TCMonad (Either LogicalKind String)

-- compPred :: Proof -> TCMonad (Either Predicate String)




compType :: Term -> TCMonad (Either Term String)

-- | TERM_TYPE
compType (Type i)  =  return (Left (Type i))

-- | TERM_VAR
compType (TermVar var) = do a <- asks (getClass (ArgNameTerm var))
                            case a of
                              Left (ArgClassTerm theType) -> 
                                do b <- (compType theType)
                                   case b of
                                     Left (Type i) -> return (Left theType)
                                     Left _ -> return (Right "undefined")
                                     Right s -> 
                                         return (Right $ "the type of the variable " ++show(var) ++ " is ill-typed.")
                              Left _ -> return (Right "undefined")
                              Right s -> return (Right s)

-- | TERM_PI, TERM_PiPredicate, !! need to expand.
compType (Pi b stage) = do
                   ((name, Embed (ArgClassTerm t1)), t2) <- unbind b
                   theKind <- compType t1
                   case theKind of
                      Left (Type i) -> local (M.insert name (ArgClassTerm t1, NonValue)) (compType t2)
                      Left _ -> return (Right "undefined")                  
                      -- FTP(For Test Purpose): return (Right (show t2))
                      Right s -> return (Right s)




-- | TermApplication Term Arg Stage


-- compType (TermApplication t a stage) = do
--                      A <- compType a
--                      b <- compType t
--                     ((name, Embed (ArgClassTerm A), t')) <- unbind b
--                     app b (a, A)




-- test code 
sample = M.fromList [((ArgNameTerm (string2Name "nat")),(ArgClassTerm (Type 0), Value))]

test :: IO()
test = do c <- runFreshMT (runReaderT (runTCMonad (compType (Pi (bind (ArgNameTerm (string2Name "x"), Embed (ArgClassTerm (Type 56))) (TermVar (string2Name "nat"))) Plus ))) sample)
          print c

-- checkData :: Datatypedecl -> IO ()
-- checkData Datatypedecl t1 t2 branches =         checkTerm
