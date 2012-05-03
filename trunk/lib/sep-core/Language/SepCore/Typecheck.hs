{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

module Language.SepCore.Typecheck where
import Prelude hiding (pred)
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
compSK (Formula i) = return (Left (Logical (i+1)))

-- | LK_Predicate
compSK (QuasiForall b) = do ((name, Embed a), lk) <- unbind b
                            case a of
                              ArgClassTerm t -> 
                                do theType <-compType t
                                   case theType of 
                                     Left (Type i) -> do
                                                  c <- local (M.insert name (ArgClassTerm t, NonValue)) (compSK lk)
                                                  case c of
                                                    Left (Logical j) -> return (Left (Logical (max (i+1) j)))
                                                    Right s -> return (Right s)
                                     Left _ -> return (Right "undefined")
                                     Right s -> return (Right s)
                              ArgClassPredicate p -> 
                                do theKind <- compLK p
                                   case theKind of 
                                     Left (Formula i) -> do
                                                  c <- local (M.insert name (ArgClassPredicate p, NonValue)) (compSK lk)
                                                  case c of
                                                    Left (Logical j) -> return (Left (Logical (max (i+1) j)))
                                                    Right s -> return (Right s)
                                     Left _ -> return (Right "undefined")
                                     Right s -> return (Right s)
                              _ -> return (Right "undefined")


compLK :: Predicate -> TCMonad (Either LogicalKind String)

-- | Predicate_Var
compLK (PredicateVar p) = do a <- asks (getClass (ArgNamePredicate p))
                             case a of
                                   Left (ArgClassLogicalKind theKind) -> 
                                        do b <- (compSK theKind)
                                           case b of
                                                Left ( Logical i) -> return (Left theKind)
                                                Right s -> 
                                                      return (Right $ "the logicalkind of the predicate variable " ++show(p) ++ " is ill-formed.")
                                   Left _ -> return (Right "undefined")
                                   Right s -> return (Right s)

-- | Predicate_Bottom
compLK (Bottom i) = return (Left (Formula i))

-- | Predicate_Terminates
compLK (Terminate t) = do theType <- compType t
                          case theType of
                               Left _ -> return (Left (Formula 0))
                               Right s -> return (Right s)

-- | Predicate_k_EQ
compLK (Equal t1 t2) = do theType1 <- compType t1
                          theType2 <- compType t2
                          case theType1 of
                               Left _ -> case theType2 of
                                              Left _ -> return (Left (Formula 0))
                                              Right s -> return (Right s)
                               Right s -> return (Right s)


-- | Predicate_forall 1,2,3,4
compLK (Forall b) = do ((argname, Embed argclass),pred) <- unbind b
                       case argclass of
                            ArgClassPredicate p -> do lk <- compLK p
                                                      case lk of
                                                           Left lk' -> do sk <- compSK lk'
                                                                          case sk of
                                                                               Left (Logical i) -> do
                                                                                    theKind <- local (M.insert argname (ArgClassPredicate p, NonValue)) (compLK pred)
                                                                                    case theKind of
                                                                                         Left (Formula j) -> return (Left (Formula (max i j)))
                                                                                         Left _ -> return (Right "undefine")
                                                                                         Right s -> return (Right s)
                                                                               Right s -> return (Right s)
                                                           Right s -> return (Right s)
                            ArgClassTerm t -> do ty <- compType t
                                                 case ty of
                                                      Left (Type i) ->  do theKind <- local (M.insert argname (ArgClassTerm t, NonValue)) (compLK pred)
                                                                           case theKind of 
                                                                                Left(Formula j) -> if i==0 then return (Left (Formula (max j 1))) else return (Left (Formula (max j i)))
                                                                                Left _ -> return (Right "undefine")
                                                                                Right s -> return (Right s)
                                                      Left _ -> return (Right "undefine")
                                                      Right s -> return (Right s)
                            ArgClassLogicalKind lk -> do sk <- compSK lk
                                                         case sk of
                                                             Left (Logical i) -> do theKind <- local (M.insert argname (ArgClassLogicalKind lk, NonValue)) (compLK pred)
                                                                                    case theKind of
                                                                                         Left (Formula j) -> return (Left (Formula (max i j)))
                                                                                         Left _ -> return (Right "undefine")
                                                                                         Right s -> return (Right s)
                                                             Right s -> return (Right s)

-- | Predicate_Lam
compLK (PredicateLambda b) = do ((argname, Embed argclass),pred) <- unbind b
                                case argclass of
                                      ArgClassPredicate p -> do lk <- compLK p
                                                                case lk of
                                                                     Left lk' -> do theKind <- local (M.insert argname (ArgClassPredicate p, NonValue)) (compLK pred)
                                                                                    case theKind of
                                                                                         Left k -> return (Left(QuasiForall (bind (argname, Embed (ArgClassPredicate p)) k)))
                                                                                         Right s -> return (Right s)
                                                                     Right s -> return (Right s)
                                      ArgClassTerm t -> do ty <- compType t
                                                           case ty of
                                                                 Left ty' ->  do theKind <- local (M.insert argname (ArgClassTerm t, NonValue)) (compLK pred)
                                                                                 case theKind of 
                                                                                       Left k -> return (Left(QuasiForall (bind (argname, Embed (ArgClassTerm t)) k)))
                                                                                       Right s -> return (Right s)
                                                                 Right s -> return (Right s)
                                      ArgClassLogicalKind lk -> do sk <- compSK lk
                                                                   case sk of
                                                                        Left sk' -> do theKind <- local (M.insert argname (ArgClassLogicalKind lk, NonValue)) (compLK pred)
                                                                                       case theKind of
                                                                                              Left k -> return (Left(QuasiForall (bind (argname, Embed (ArgClassLogicalKind lk)) k)))
                                                                                              Right s -> return (Right s)
                                                                        Right s -> return (Right s)

-- | Predicate_app
compLK (PredicateApplication p a) = do b <- compLK p
                                       case b of
                                         Left (QuasiForall b') -> do ((argname, Embed argclass),lk) <- unbind b' 
                                                                     case argname of
                                                                       ArgNameTerm at ->
                                                                           case a of
                                                                             ArgTerm t -> do theType <- compType t
                                                                                             case theType of
                                                                                                  Left t' -> 
                                                                                                      if aeq argclass (ArgClassTerm t') then return (Left (subst at t lk))
                                                                                                      else return (Right $ "Expected type: " ++show(argclass)++ ". Actual type: " ++ show(ArgClassTerm t') )
                                                                                                  Right s -> return (Right s)
                                                                             _ -> return (Right $ "Expected argument should be a term")
                                                                       ArgNamePredicate pt ->
                                                                           case a of
                                                                             ArgPredicate pred -> do theKind <- compLK pred
                                                                                                     case theKind of
                                                                                                              Left k -> if aeq argclass (ArgClassLogicalKind k) then return (Left (subst pt pred lk))
                                                                                                                        else return (Right $ "Expected logical kind: " ++show(argclass)++ ". Actual kind: " ++ show(ArgClassLogicalKind k) )
                                                                                                              Right s -> return (Right s)
                                                                             _ -> return (Right $ "Expected argument should be a predicate")
                                                                       ArgNameProof prt->
                                                                                  case a of
                                                                             ArgProof pr -> do theP <- compPred pr
                                                                                               case theP of
                                                                                                     Left p' -> if aeq argclass (ArgClassPredicate p') then return (Left (subst prt pr lk))
                                                                                                                else return (Right $ "Expected Predicate: " ++show(argclass)++ ". Actual predicate: " ++ show(ArgClassPredicate p') )
                                                                                                     Right s -> return (Right s)
                                         Left _ -> return (Right $ "The predicate "++show(p)++ " is ill-formed")
                                         Right s -> return (Right s)
                                         

compPred :: Proof -> TCMonad (Either Predicate String)

-- | Proof_Var
compPred (ProofVar p) = do a <- asks (getClass (ArgNameProof p))
                           case a of
                                   Left (ArgClassPredicate thePred) -> 
                                        do b <- (compLK thePred)
                                           case b of
                                                Left _ -> return (Left thePred)
                                                Right s -> 
                                                      return (Right $ "the predicate of the proof variable " ++show(p) ++ " is ill-formed.")
                                   Left _ -> return (Right "undefined")
                                   Right s -> return (Right s)

-- | Proof_ForallTerm, ForallPredicate, ForallLK
compPred (ProofLambda b) = do ((argname, Embed argclass), p) <- unbind b
                              case argclass of
                                ArgClassTerm t -> do theType <- compType t
                                                     case theType of
                                                       Left (Type i) -> do thePred <- local (M.insert argname (ArgClassTerm (Type i), NonValue)) (compPred p)
                                                                           case thePred of
                                                                             Left pred -> return (Left(Forall (bind (argname, Embed (ArgClassTerm t)) pred)))
                                                                             Right s -> return (Right s)
                                                       Left _ -> return (Right $ "The type of the term " ++show(t)++" is ill-typed")
                                                       Right s -> return (Right s)
                                ArgClassPredicate pred -> do theKind <- compLK pred
                                                             case theKind of
                                                               Left k -> do sk <- compSK k
                                                                            case sk of
                                                                              Left (Logical i) -> do
                                                                                      thePred <- local (M.insert argname (ArgClassPredicate pred, Value)) (compPred p)
                                                                                      case thePred of
                                                                                        Left pred' -> return (Left(Forall (bind (argname, Embed (ArgClassPredicate pred)) pred')))
                                                                                        Right s -> return(Right s)
                                                                              Right s -> return(Right s) 
                                                               Right s -> return(Right s)
                                ArgClassLogicalKind lk -> do sk <- compSK lk
                                                             case sk of
                                                               Left (Logical i) -> do 
                                                                       thePred <- local (M.insert argname (ArgClassLogicalKind lk, Value)) (compPred p)
                                                                       case thePred of
                                                                         Left pred' -> return (Left(Forall (bind (argname, Embed (ArgClassLogicalKind lk)) pred')))
                                                                         Right s -> return(Right s) 
                                                               Right s -> return(Right s) 

-- | Proof_app
compPred (ProofApplication p a) = do b <- compPred p
                                     case b of
                                         Left (Forall b') -> do ((argname, Embed argclass),pr) <- unbind b' 
                                                                case argname of
                                                                       ArgNameTerm at ->
                                                                           case a of
                                                                             ArgTerm t -> do theType <- compType t
                                                                                             case theType of
                                                                                                  Left t' -> 
                                                                                                      if aeq argclass (ArgClassTerm t') then return (Left (subst at t pr))
                                                                                                      else return (Right $ "Expected type: " ++show(argclass)++ ". Actual type: " ++ show(ArgClassTerm t') )
                                                                                                  Right s -> return (Right s)
                                                                             _ -> return (Right $ "Expected argument should be a term")
                                                                       ArgNamePredicate pt ->
                                                                           case a of
                                                                             ArgPredicate pred -> do theKind <- compLK pred
                                                                                                     case theKind of
                                                                                                              Left k -> if aeq argclass (ArgClassLogicalKind k) then return (Left (subst pt pred pr))
                                                                                                                        else return (Right $ "Expected logical kind: " ++show(argclass)++ ". Actual kind: " ++ show(ArgClassLogicalKind k) )
                                                                                                              Right s -> return (Right s)
                                                                             _ -> return (Right $ "Expected argument should be a predicate")
                                                                       ArgNameProof prt->
                                                                                  case a of
                                                                             ArgProof pro -> do theP <- compPred pro
                                                                                                case theP of
                                                                                                     Left p' -> if aeq argclass (ArgClassPredicate p') then return (Left (subst prt pro pr))
                                                                                                                else return (Right $ "Expected Predicate: " ++show(argclass)++ ". Actual predicate: " ++ show(ArgClassPredicate p') )
                                                                                                     Right s -> return (Right s)
                                         Left _ -> return (Right $ "The predicate "++show(p)++ " is ill-formed")
                                         Right s -> return (Right s)



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