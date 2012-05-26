{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

module Language.SepCore.Typecheck where
import Prelude hiding (pred,compare)
import Language.SepCore.Syntax
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

newtype TCMonad a = TCMonad{ runTCMonad :: (ReaderT Context (FreshMT Identity)) a}   
 deriving (Monad, MonadReader Context, Fresh)
type Context = M.Map ArgName (ArgClass, Value)
type Env = StateT Context (FreshMT IO)
type LocalEnv = StateT Context (FreshMT Identity)

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
                                         Left (Pi b' stage') -> 
                                                           if aeq stage stage' then
                                                               do ((argname, Embed argclass),prog) <- unbind b' 
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
                                                           else return (Right $ "The stage of the argument "++show(arg)++ "doesn't match the stage of the function")
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
                                   else return (Right $ "the term" ++show(t)++ " is not type checked. rec")
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


-- | Term_case

compType (TermCase1 t branches) = do theType <- compType t
                                     case theType of
                                       Left t' -> do
                                         theType' <- checkBranch Undefined t' branches
                                         case theType' of
                                           Right t'' -> return (Left t'')
                                           Left s -> return (Right s)
                                       Right s -> return (Right s)

-- applying a datatype constructor's type to a list of arguments
getInstance constrType@(Pi b st) (arg : cs) = do 
  ((argname, Embed argclass),res)  <- unbind b 
  case argname of
    ArgNameTerm nm -> let res' = subst (translate nm) arg res in
                      getInstance res' cs
    ArgNameProof nm -> let res' = subst (translate nm) arg res in
                      getInstance res' cs
    ArgNamePredicate nm -> let res' = subst (translate nm) arg res in
                      getInstance res' cs

getInstance constrType [] = return $ Right constrType
getInstance _ _ = return $ Left "unkown error"
        

--calculate the local context for each branch

--calcLocalContext :: Term -> Scheme -> LocalEnv (Either String Bool)
--calcLocalContext ((TermVar c):[]) _ = return $ Right True

calcLocalContext constrType@(Pi b st) (h:ls)  = do  
  env <- get  
  ((argname, Embed argclass), t) <- unbind b
  put (M.insert h (argclass, NonValue) env)
  calcLocalContext t ls 

calcLocalContext (TermVar _ ) [] = return $ Right True
calcLocalContext (TermApplication _ _ _ ) [] = return $ Right True
calcLocalContext _ _ = return $ Left "Patterns variables doesn't fit well with the constructor ."
    
sanityCheck :: Term -> [ArgName] -> Bool
sanityCheck t (argname:cs) = case argname of
                               ArgNameTerm tm -> (elem tm (fv t)) || (sanityCheck t cs) 
                               ArgNameProof pr -> (elem pr (fv t)) || (sanityCheck t cs) 
                               ArgNamePredicate pred -> (elem pred (fv t)) || (sanityCheck t cs)
sanityCheck t [] = False

-- The type of the whole case expression, the type of t in case t, branches. 
checkBranch :: Term -> Term -> TermBranches -> TCMonad (Either String Term)
checkBranch state theType ((constr, binding): l) = 
               case flatten theType of
                 Left ls -> do
                   (argnames,t1) <- unbind binding
                   env <- ask
                   case getClass constr env of
                     Left (ArgClassTerm ctype) -> 
                         case flatten ctype of
                           Left d' -> if aeq (head d') (head ls) then 
                                          do theType' <- getInstance ctype (tail ls)
                                             case theType' of
                                               Right t -> do
                                                 theType'' <- local (M.union (runIdentity (runFreshMT (execStateT (calcLocalContext t argnames) M.empty)))) (compType t1)
                                                 case theType'' of
                                                   Left t1' -> 
                                                     if not (sanityCheck t1' argnames) then  
                                                         if aeq state Undefined then checkBranch t1' theType l
                                                         else if aeq t1' state then checkBranch t1' theType l
                                                              else return $ Left $ "Expected type: " ++show(state)++". Actual type " ++show(t1')
                                                     else return $ Left $ "An insane event just happened."
                                                   Right s -> return $ Left s
                                               Left s -> return $ Left s
                                      else return $ Left $ "The actual type of the datatype constructor " ++show(constr)++ " doesn't fit the corresponding datatype "++show(head ls)
                           Right s -> return $ Left s
                     Left _ -> return $ Left $ "Couldn't find the type for " ++show(constr)
                     Right s -> return $ Left s
                 Right s -> return $ Left s

checkBranch state theType [] = return $ Right state

flatten :: Term -> Either [Arg] String
flatten (Pi b stage) = let (b1, t1) = unsafeUnbind b in
                                 case t1 of
                                   Pi c st -> flatten (Pi c st)
                                   TermApplication t a st -> case (flatten t) of 
                                                               Left ls -> Left (ls++[a])
                                                               Right s -> Right s
                                   TermVar t -> Left [ArgTerm (TermVar t)]
                                   _ -> Right "Not a standard form"

flatten (TermApplication t a st) = case (flatten t) of 
                                     Left ls -> Left (ls++[a])
                                     Right s -> Right s

flatten (TermVar t) = Left [ArgTerm (TermVar t)]
flatten _ = Right "Not a standard form"

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
-- Append a tele in front of a term
teleArrow :: Tele -> Term -> Term
teleArrow Empty end = end
teleArrow (TCons binding) end = Pi (bind (argname,argclass) arrRest) stage
 where ((argname,stage,argclass),rest) = unrebind binding
       arrRest = teleArrow rest end
teleArrowMinus :: Tele -> Term -> Term
teleArrowMinus Empty end = end
teleArrowMinus (TCons binding) end = Pi (bind (argname,argclass) arrRest) Minus
 where ((argname,stage,argclass),rest) = unrebind binding
       arrRest = teleArrowMinus rest end


checkData :: Datatypedecl -> Env (Either String Bool)
checkData (Datatypedecl dataname bindings) = do
  (tele, cs) <- unbind bindings
  env <- get
  let datatype = teleArrow tele (Type 0)
  case dataname of
      TermVar x ->  case runIdentity (runFreshMT (runReaderT (runTCMonad (compType datatype)) env)) of
                      Left (Type i) -> do
                        put (M.insert (ArgNameTerm x)  (ArgClassTerm datatype, NonValue) env)
                        checkConstructors dataname tele cs
                      _ -> return $ Left $ "The type of "++show(x)++ " is not well-typed."
      _ -> return $ Left $ "unkown error"


--compare :: Monad M => [Arg] -> Tele -> M Bool
--compare the order of [arg] and Tele
compare [] Empty = return $ Left True
compare (h:l) (TCons bindings) = do let ((argname,stage ,argclass),res) = unrebind bindings
                                    case argname of
                                      ArgNameTerm u ->
                                          case h of
                                            ArgTerm (TermVar x) ->  
                                                if aeq x u then compare l res
                                                else return $ Left False
                                            _ -> return $ Left False
                                      ArgNameProof u ->
                                          case h of
                                            ArgProof (ProofVar x) ->  
                                                if aeq x u then compare l res
                                                else return $ Left False
                                            _ -> return $ Left False
                                      ArgNamePredicate u ->
                                          case h of
                                            ArgPredicate (PredicateVar x) ->  
                                                if aeq x u then compare l res
                                                else return $ Left False
                                            _ -> return $ Left False

compare _ _ = return $ Right "error"


checkConstructors :: Term -> Tele -> [(ArgName, Term)] -> Env (Either String Bool)

checkConstructors dataname _ [] = return $ Right True
checkConstructors dataname tele ((constr,t2):l) = do 
  env <- get
  case dataname of
    TermVar d -> 
        case constr of
          ArgNameTerm c -> case flatten t2 of
                         Left ls -> if aeq (head ls) (ArgTerm dataname) then
                                        do result <- compare (tail ls) tele
                                           case result of
                                             Left True -> 
                                                 let t2' = teleArrow tele t2 in
                                                 case runIdentity (runFreshMT (runReaderT (runTCMonad (compType t2')) env)) of
                                                   Left (Type i) -> do
                                                         put (M.insert (ArgNameTerm c)  (ArgClassTerm t2', NonValue) env)
                                                         checkConstructors dataname tele l
                                                   _ -> return $ Left $ "The type of the data constructor "++show(c)++ " is not well-typed. 0"
                                             Left False -> return $ Left $ "The type of the data constructor "++show(c)++ " is not well-formed 1." 
                                             Right _ -> return $ Left $ "The type of the data constructor "++show(c)++ " is not well-formed 3." 
                                     else return $ Left $ "The type of the data constructor "++show(c)++ " is not well-formed 2." 
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
                    _ -> return $ Left $ "The type of " ++show(t')++" is not well-typed. -- checkProgDecl"
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
                    Right s -> return $ Left $ "The type of " ++show(t')++" is not well-typed. --checkProgDef" ++ show(s)
    _ -> return $ Left $ "unkown error"





-- test code 

{-
sample = M.fromList [((ArgNameTerm (string2Name "nat")),(ArgClassTerm (Type 0), Value))]

test :: IO()
test = do c <- runFreshMT (runReaderT (runTCMonad (compType (Pi (bind (ArgNameTerm (string2Name "x"), Embed (ArgClassTerm (Type 56))) (TermVar (string2Name "nat"))) Plus ))) sample)
          print c
-}
