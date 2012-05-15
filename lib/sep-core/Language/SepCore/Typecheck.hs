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

newtype TCMonad a = TCMonad{ runTCMonad :: (ReaderT Context (FreshMT Identity)) a}   
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
                                                       Left (Type i) -> do thePred <- local (M.insert argname (ArgClassTerm t, NonValue)) (compPred p)
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

-- | TERM_PI, TERM_PiPredicate, TERM_PILK
compType (Pi b stage) = do ((argname, Embed argclass), prog) <- unbind b
                           case argclass of
                                ArgClassTerm t -> do theType <- compType t
                                                     case theType of
                                                       Left (Type 0) -> local (M.insert argname (ArgClassTerm t, NonValue)) (compType prog)
                                                       Left _ -> return (Right $ "The type of the term " ++show(t)++" is ill-typed")
                                                       Right s -> return (Right s)
                                ArgClassPredicate pred -> do theKind <- compLK pred
                                                             case theKind of
                                                               Left k -> do sk <- compSK k
                                                                            case sk of
                                                                              Left (Logical i) -> local (M.insert argname (ArgClassPredicate pred, NonValue)) (compType prog)
                                                                              Right s -> return(Right s) 
                                                               Right s -> return(Right s)
                                ArgClassLogicalKind lk -> do sk <- compSK lk
                                                             case sk of
                                                               Left (Logical i) -> local (M.insert argname (ArgClassLogicalKind lk, NonValue)) (compType prog)
                                                               Right s -> return(Right s) 

-- | Term_LamMinus, LamPlus, LamIMPI, notice here for LamMinus, I implement x \notin FV(t) but not x \notin FV(|t|). 
compType (TermLambda b stage) = do ((argname, Embed argclass), prog) <- unbind b
                                   case argclass of
                                     ArgClassTerm t -> case stage of
                                                    Plus -> do
                                                      theType <- local (M.insert argname (ArgClassTerm t, Value)) (compType prog)
                                                      case theType of
                                                        Left t' -> return (Left(Pi (bind (argname, Embed (ArgClassTerm t)) t') Plus))
                                                        Right s -> return (Right s)
                                                    Minus -> case argname of
                                                               ArgNameTerm tname -> if elem tname (fv prog) then return (Right "undefined")
                                                                                else do theType <- local (M.insert argname (ArgClassTerm t, NonValue)) (compType prog)
                                                                                        case theType of
                                                                                          Left t' -> return (Left(Pi (bind (argname, Embed (ArgClassTerm t)) t') Minus))
                                                                                          Right s -> return (Right s)
                                                               _ -> return (Right "undefined")
                                     ArgClassPredicate pred -> do 
                                              theType <- local (M.insert argname (ArgClassPredicate pred, NonValue)) (compType prog)
                                              case theType of
                                                Left ty -> return (Left(Pi (bind (argname, Embed (ArgClassPredicate pred)) ty) Minus))
                                                Right s -> return(Right s)
                                     ArgClassLogicalKind lk -> do
                                              theType <- local (M.insert argname (ArgClassLogicalKind lk, NonValue)) (compType prog)
                                              case theType of
                                                Left ty -> return (Left(Pi (bind (argname, Embed (ArgClassLogicalKind lk)) ty) Minus))
                                                Right s -> return(Right s) 
                                                

-- | Term_APP
compType (TermApplication term arg stage) = do 
                                    b <- compType term
                                    case b of
                                         Left (Pi b' stage') -> do ((argname, Embed argclass),prog) <- unbind b' 
                                                                   case argname of
                                                                       ArgNameTerm at ->
                                                                           case arg of
                                                                             ArgTerm t -> do theType <- compType t
                                                                                             case theType of
                                                                                                  Left t' -> 
                                                                                                      if aeq argclass (ArgClassTerm t') then return (Left (subst at t prog))
                                                                                                      else return (Right $ "Expected type: " ++show(argclass)++ ". Actual type: " ++ show(ArgClassTerm t') )
                                                                                                  Right s -> return (Right s)
                                                                             _ -> return (Right $ "Expected argument should be a term")
                                                                       ArgNamePredicate pt ->
                                                                           case arg of
                                                                             ArgPredicate pred -> do theKind <- compLK pred
                                                                                                     case theKind of
                                                                                                              Left k -> if aeq argclass (ArgClassLogicalKind k) then return (Left (subst pt pred prog))
                                                                                                                        else return (Right $ "Expected logical kind: " ++show(argclass)++ ". Actual kind: " ++ show(ArgClassLogicalKind k) )
                                                                                                              Right s -> return (Right s)
                                                                             _ -> return (Right $ "Expected argument should be a predicate")
                                                                       ArgNameProof prt->
                                                                                  case arg of
                                                                             ArgProof pro -> do theP <- compPred pro
                                                                                                case theP of
                                                                                                     Left p' -> if aeq argclass (ArgClassPredicate p') then return (Left (subst prt pro prog))
                                                                                                                else return (Right $ "Expected Predicate: " ++show(argclass)++ ". Actual predicate: " ++ show(ArgClassPredicate p') )
                                                                                                     Right s -> return (Right s)
                                         Left _ -> return (Right $ "The term "++show(term)++ " is ill-formed")
                                         Right s -> return (Right s)

-- | Term abort
compType (Abort t) = do theType <- compType t
                        case theType of
                          Left (Type i) -> return (Left t)
                          Left _ -> return (Right "unknown from term-abort")
                          Right s -> return (Right s)

-- | Term_REC
compType (Rec b) = do ((x, f, Embed (Pi t' Plus)), t) <- unbind b
                      ((y, Embed t1), t2) <- unbind t'
                      theType <- local((M.insert (ArgNameTerm f) (ArgClassTerm (Pi (bind (y, Embed t1) t2) Plus), Value)) . (M.insert (ArgNameTerm x) (t1, Value))) (compType t)
                      case theType of
                        Left ty -> if aeq t2 ty then return (Left (Pi (bind (y, Embed t1) t2) Plus))
                                   else return (Right $ "the term" ++show(t)++ " is not type checked.")
                        Right s -> return (Right s)

-- | Term_let

compType (TermLetTerm1 b t) = do (x, t1) <- unbind b
                                 theType <- compType t
                                 case theType of 
                                   Left t' -> (local (M.insert (ArgNameTerm x) (ArgClassTerm t', NonValue)) (compType t1))
                                   Right s -> return (Right s)

compType (TermLetProof b p) = do (x, t1) <- unbind b
                                 thePred <- compPred p
                                 case thePred of 
                                   Left pred -> (local (M.insert (ArgNameProof x) (ArgClassPredicate pred, NonValue)) (compType t1))
                                   Right s -> return (Right s)

type Env = StateT Context IO
type LocalEnv = StateT Context (FreshMT Identity)

-- | Term_case
-- compType (TermCase1 t branches) = do theType <- compType t
--                                      case theType of
--                                        Left (TermVar d) -> 
--                                         checkBranch Undefined theType branches
                                                                               
                                                                                      
--                                        Left (TermApplication t arg st) -> 
--                                        Left _ -> return (Right $ show(t)++"is not well-typed")
--                                        Right s -> return (Right s)


calcLocalContext :: TermScheme -> Term -> LocalEnv (Either String Bool)
calcLocalContext ((TermVar c):[]) _ = return $ Right True
calcLocalContext ((TermVar c):l) (Pi b st) = do  
  ((argname, Embed argclass),res)  <- unbind b 
  env <- get
  case head l of
    TermVar u -> do put (M.insert (ArgNameTerm u) (argclass, NonValue) env)
                    calcLocalContext l res 
    _ -> return $ Left "Incorrect pattern."

calcLocalContext _ _ = return $ Left "Patterns variables doesn't fit well with the constructor ."
    

-- checkBranch :: Term -> Term -> TermBranches -> TCMonad (Either String Term)
-- checkBranch state theType ((c:sch, t1): l) = do 
--   case state of
--     Undefined -> do 
--                case unWrap theType of
--                  Left dataname -> do
--                    env <- ask
--                    case getClass (ArgNameTerm c) env of
--                      Left (ArgClassTerm ctype) -> 
--                          case unWrap ctype of
--                            Left d' -> if aeq d' dataname then 
                                          
                                           
                                                                    
                                                                    





unWrap :: Term -> Either Term String
unWrap (Pi b stage) = let (b1, t1) = unsafeUnbind b in
                      case t1 of
                        Pi c st -> unWrap (Pi c st)
                        TermApplication t a st -> Left t
                        TermVar t -> Left (TermVar t)
                        _ -> Right "Not a standard form"
unWrap (TermApplication t a st) = Left t
unWrap (TermVar t) = Left (TermVar t)
unWrap _ = Right "Not a standard form"
typechecker :: Module -> Env String

typechecker [] = return "Type checker seems to approve your program, so congratulation!"

typechecker ((DeclData d):l) = do s <- checkData d
                                  case s of 
                                    Left str -> return str
                                    Right _ -> typechecker l


typechecker ((DeclProgdecl p):l) = do s <- checkProgDecl p
                                      case s of 
                                        Left str -> return str
                                        Right _ -> typechecker l


typechecker ((DeclProgdef p):l) = do  s <- checkProgDef p
                                      case s of 
                                        Left str -> return str
                                        Right _ -> typechecker l



-- type-check data type declaration
checkData :: Datatypedecl -> Env (Either String Bool)
checkData (Datatypedecl dataname datatype constructors) = do
  env <- get
  case dataname of
    TermVar x ->  case runIdentity (runFreshMT (runReaderT (runTCMonad (compType datatype)) env)) of
                    Left (Type i) -> do
                      put (M.insert (ArgNameTerm x)  (ArgClassTerm datatype, NonValue) env)
                      checkConstructors dataname constructors
                    _ -> return $ Left $ "The type of "++show(dataname)++ " is not well-typed."
    _ -> return $ Left $ "unkown error"

checkConstructors :: Term -> [(Term, Term)] -> Env (Either String Bool)

checkConstructors dataname [] = return $ Right True
checkConstructors dataname ((t1,t2):l) = do 
  env <- get
  case dataname of
    TermVar d -> 
        case t1 of
          TermVar c -> case unWrap t2 of
                         Left t2' -> if aeq dataname t2' then
                                         case runIdentity (runFreshMT (runReaderT (runTCMonad (compType t2)) env)) of
                                           Left (Type i) -> do
                                             put (M.insert (ArgNameTerm c)  (ArgClassTerm t2, NonValue) env)
                                             checkConstructors dataname l
                                           _ -> return $ Left $ "The type of the data constructor "++show(c)++ " is not well-typed."                                      else return $ Left $ "The type of the data constructor "++show(c)++ " is not well-formed." 
                         Right _ -> return $ Left $ "The type of the data constructor "++show(c)++ " is not well-formed." 
          _ -> return $ Left $ "unkown error"
    _ -> return $ Left $ "unkown error"

-- type-check program declaration

checkProgDecl :: Progdecl -> Env (Either String Bool)
checkProgDecl (Progdecl t t') = do
  env <- get
  case t of
    TermVar x -> case runIdentity (runFreshMT (runReaderT (runTCMonad (compType t')) env)) of
                    Left (Type i) -> do
                      put (M.insert (ArgNameTerm x)  (ArgClassTerm t', NonValue) env)
                      return (Right True)
                    _ -> return $ Left $ "The type of " ++show(t')++" is not well-typed"
    _ -> return $ Left $ "unkown error"

-- type-check program definition
checkProgDef :: Progdef -> Env (Either String Bool)
checkProgDef (Progdef t t') = do
  env <- get
  case t of
    TermVar x -> case runIdentity (runFreshMT (runReaderT (runTCMonad (compType t')) env)) of
                    Left t'' -> case (getClass (ArgNameTerm x) env) of
                                Left t1 -> if aeq t1 (ArgClassTerm t'') then return (Right True) else return $ Left $ "Expecting "++show(t1)++ ", but actually getting " ++show(t'') 
                                _ -> return $ Left $ "Can't find "++show (x)++ " from the context, it is not defined."
                    _ -> return $ Left $ "The type of " ++show(t')++" is not well-typed"
    _ -> return $ Left $ "unkown error"





-- test code 

{-
sample = M.fromList [((ArgNameTerm (string2Name "nat")),(ArgClassTerm (Type 0), Value))]

test :: IO()
test = do c <- runFreshMT (runReaderT (runTCMonad (compType (Pi (bind (ArgNameTerm (string2Name "x"), Embed (ArgClassTerm (Type 56))) (TermVar (string2Name "nat"))) Plus ))) sample)
          print c
-}
