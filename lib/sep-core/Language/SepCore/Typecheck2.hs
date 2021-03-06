{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

module Language.SepCore.Typecheck2 where
import Prelude hiding (pred,compare, zipWith)
import Language.SepCore.Syntax
import Language.SepCore.PrettyPrint
import Language.SepCore.Lexer
import Language.SepCore.Error
import Language.SepCore.Monad
import Language.SepCore.Erasure
import Language.SepCore.Rewriting
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

-- \Gamma |- LK : Logical i

compSK :: LogicalKind -> TCMonad SuperKind

-- | LK_Formula
compSK (Formula i) = return (Logical (i+1))

-- | LK_Predicate
compSK (QuasiForall b) = do ((name, Embed a), lk) <- unbind b
                            case a of
                              ArgClassTerm t -> do
                                     (Type i) <- (compType t) >>= ensureType 
                                     (Logical j) <- (withVar name (ArgClassTerm t, NonValue)) (compSK lk)
                                     return  (Logical (max (i+1) j))
                              ArgClassPredicate p -> do
                                     (Formula i) <- compLK p >>= ensureFormula
                                     (Logical j) <- (withVar name (ArgClassPredicate p, NonValue)) (compSK lk)
                                     return  (Logical (max (i+1) j))
                              _ -> typeError $ disp "unsupport argClass for " <+> disp (QuasiForall b)

compSK (PosLK p lk) = compSK lk `catchError` addErrorPos p (ExprLK lk)

compLK :: Predicate -> TCMonad LogicalKind 

compLK (PosPredicate p pred) = compLK pred `catchError`addErrorPos p (ExprPred pred)

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
      (Formula j)  <- ensureFormula =<< ((withVar argname (ArgClassPredicate p, NonValue)) (compLK pred)) 
      return  (Formula (max i j))
    ArgClassTerm t -> do 
      (Type i) <- compType t >>= ensureType
      (Formula j) <-  (withVar argname (ArgClassTerm t, NonValue)) (compLK pred) >>= ensureFormula
      if i==0 then return (Formula (max j 1)) else return (Formula (max j i))
    ArgClassLogicalKind lk -> do 
      (Logical i) <- compSK lk
      (Formula j) <- (withVar argname (ArgClassLogicalKind lk, NonValue)) (compLK pred) >>= ensureFormula
      return  (Formula (max i j))

-- | Predicate_Lam
compLK (PredicateLambda b) = do 
  ((argname, Embed argclass),pred) <- unbind b
  case argclass of
    ArgClassPredicate p -> do 
      compLK p
      theKind <-  (withVar argname (ArgClassPredicate p, NonValue)) (compLK pred)
      return (QuasiForall (bind (argname, Embed (ArgClassPredicate p)) theKind))
    ArgClassTerm t -> do 
      compType t >>= ensureType
      theKind <-  (withVar argname (ArgClassTerm t, NonValue)) (compLK pred)
      return (QuasiForall (bind (argname, Embed (ArgClassTerm t)) theKind))     
    ArgClassLogicalKind lk -> do 
       compSK lk
       theKind <- (withVar argname (ArgClassLogicalKind lk, NonValue)) (compLK pred)
       return (QuasiForall (bind (argname, Embed (ArgClassLogicalKind lk)) theKind))
    
-- | Predicate_app
compLK (PredicateApplication p a) = do 
  (QuasiForall b) <- compLK p >>= ensureQForall 
  ((argname, Embed argclass),lk) <- unbind b 
  case argname of
    ArgNameTerm at -> do
        t <- ensureArgTerm a 
        theType <- compType t
        if aeq argclass (ArgClassTerm theType) then return (subst at t lk) else typeError $ disp ("Expected type: ") <+>disp(argclass) <+> disp(" Actual type:")<+> disp(ArgClassTerm theType) 
    ArgNamePredicate pt -> do
        pred <- ensureArgPredicate a 
        theKind <- compLK pred
        if aeq argclass (ArgClassLogicalKind theKind) then return (subst pt pred lk) else typeError $ disp ("Expected logical kind:")<+> disp(argclass) <+> disp ("Actual kind:")<+> disp(ArgClassLogicalKind theKind)
    ArgNameProof prt-> do
        pr <- ensureArgProof a
        theP <- compPred pr
        if aeq argclass (ArgClassPredicate theP) then return (subst prt pr lk) else typeError $ disp ("Expected Predicate:")<+>disp(argclass) <+> disp ("Actual predicate:")<+> disp (ArgClassPredicate theP) 
        

compPred :: Proof -> TCMonad Predicate

compPred (PosProof p prf) = compPred prf `catchError` addErrorPos p (ExprProof prf)

-- | Proof_Var
compPred (ProofVar p) = do 
  thePred <- (getClass (ArgNameProof p)) >>= ensureArgClassPred
  compLK thePred
  return thePred
  
-- | Proof_ForallTerm, ForallPredicate, ForallLK
compPred (ProofLambda b) = do 
  ((argname, Embed argclass), p) <- unbind b
  case argclass of
    ArgClassTerm t -> do  
      compType t >>= ensureType
      thePred <-  (withVar argname (ArgClassTerm t, NonValue)) (compPred p)
      return (Forall (bind (argname, Embed (ArgClassTerm t)) thePred))
    ArgClassPredicate pred -> do 
      compLK pred >>= compSK
      thePred <- (withVar argname (ArgClassPredicate pred, Value)) (compPred p)
      return (Forall (bind (argname, Embed (ArgClassPredicate pred)) thePred))
    ArgClassLogicalKind lk -> do 
       compSK lk 
       thePred <- (withVar argname (ArgClassLogicalKind lk, Value)) (compPred p)
       return (Forall (bind (argname, Embed (ArgClassLogicalKind lk)) thePred))

compPred (Join t1 t2) = do 
  compType t1
  compType t2
  t1' <- erase t1
  t2' <- erase t2
  r <- joinable t1' 1000 t2' 1000
  if r then return $ Equal t1 t2 else typeError $ disp t1 <+> disp "is not joinable with" <+> disp t2 <+> disp "in 1000 steps."

-- | Proof_app
compPred (ProofApplication p a) = do 
  (Forall b) <- compPred p >>= ensureForall
  ((argname, Embed argclass),pr) <- unbind b
  case argname of
    ArgNameTerm at -> do 
      t <- ensureArgTerm a 
      theType <- compType t
      if aeq argclass (ArgClassTerm theType) then return (subst at t pr) else typeError $ disp ("Expected type: ") <+>disp(argclass)<+> disp("Actual type:")<+> disp (ArgClassTerm theType) 
    ArgNamePredicate pt -> do
      pred <- ensureArgPredicate a 
      theKind <- compLK pred
      if aeq argclass (ArgClassLogicalKind theKind) then return (subst pt pred pr)else typeError $ disp( "Expected logical kind:")<+>disp(argclass)<+>disp( "Actual kind:")<+> disp(ArgClassLogicalKind theKind)
    ArgNameProof prt-> do
      pro <- ensureArgProof a
      theP <- compPred pro
      if aeq argclass (ArgClassPredicate theP) then return (subst prt pro pr) else typeError $ disp("Expected Predicate:")<+>disp(argclass)<+> disp(" Actual predicate:")<+> disp(ArgClassPredicate theP) 
                    
compType :: Term -> TCMonad Term

compType (Pos p t) = compType t `catchError`addErrorPos p (ExprTerm t)

-- | TERM_TYPE
compType (Type i)  =  return (Type i)

-- | TERM_VAR
compType (TermVar var) = do 
  theType <- (getClass (ArgNameTerm var)) >>= ensureArgClassTerm
  compType theType >>= ensureType
  return theType
                  
-- | TERM_PI, TERM_PiPredicate, TERM_PILK
compType (Pi b stage) = do 
  ((argname, Embed argclass), prog) <- unbind b
  case argclass of
    ArgClassTerm t -> do 
      compType t >>= ensureType
      ensureType =<< (withVar argname (ArgClassTerm t, NonValue)) (compType prog)
    ArgClassPredicate pred -> do 
      compLK pred >>= compSK
      (withVar argname (ArgClassPredicate pred, NonValue)) (compType prog) >>= ensureType
    ArgClassLogicalKind lk -> do 
      compSK lk
      (withVar argname (ArgClassLogicalKind lk, NonValue)) (compType prog) >>= ensureType


-- | Term_LamPlus 
compType (TermLambda b Plus) = do 
  ((argname, Embed argclass), prog) <- unbind b
  t <- ensureArgClassTerm argclass  
  theType <- (withVar argname (ArgClassTerm t, Value)) (compType prog)
  return (Pi (bind (argname, Embed (ArgClassTerm t)) theType) Plus)
                                                        
-- | Term_LambPred LambLK
compType (TermLambda b Minus) = do 
  ((argname, Embed argclass), prog) <- unbind b
  case argclass of
    ArgClassPredicate pred -> do 
      theType <- (withVar argname (ArgClassPredicate pred, NonValue)) (compType prog)
      return (Pi (bind (argname, Embed (ArgClassPredicate pred)) theType) Minus)
    ArgClassLogicalKind lk -> do
      theType <- (withVar argname (ArgClassLogicalKind lk, NonValue)) (compType prog)
      return (Pi (bind (argname, Embed (ArgClassLogicalKind lk)) theType) Minus)
    ArgClassTerm t -> do -- This case may be changed after I implement the erasure function.
      theType <- (withVar argname (ArgClassTerm t, NonValue)) (compType prog)
      return (Pi (bind (argname, Embed (ArgClassTerm t)) theType) Minus)
                                                                
-- | Term_App
compType (TermApplication term arg stage) = do 
  (Pi b' stage') <- compType term >>= ensurePi 
  if aeq stage stage' then
      do ((argname, Embed argclass),prog) <- unbind b' 
         case argname of
           ArgNameTerm at -> do
             t <- ensureArgTerm arg  
             theType <- compType t
             if aeq argclass (ArgClassTerm theType) then return (subst at t prog) else typeError $ disp("Expected type:") <+>disp(argclass)<+> disp("Actual type:") <+> disp(ArgClassTerm theType) 
           ArgNamePredicate pt -> do
             pred <-ensureArgPredicate arg 
             theKind <- compLK pred
             if aeq argclass (ArgClassLogicalKind theKind) then return (subst pt pred prog) else typeError $ disp("Expected logical kind:") <+>disp(argclass)<+>disp( "Actual kind:") <+> disp(ArgClassLogicalKind theKind)
           ArgNameProof prt-> do
              pro <- ensureArgProof arg
              theP <- compPred pro
              if aeq argclass (ArgClassPredicate theP) then return (subst prt pro prog) else typeError $ disp("Expected Predicate: ")<+>disp(argclass)<+> disp("Actual predicate:") <+> disp (ArgClassPredicate theP)  else typeError $ disp("The stage of the argument")<+>disp(arg)<+>disp( "doesn't match the stage of function")<+>disp(term)

-- | Term abort
compType (Abort t) = do  
  compType t >>= ensureType
  return t

-- | Term_REC
compType (Rec b) = do 
  ((x, f, Embed pa), t) <- unbind b 
  (Pi t' st) <- ensurePi pa
  case st of
    Minus -> typeError $ disp("stage error")
    Plus -> do
      ((y, Embed t1), t2) <- unbind t'
      theType <- ((withVar (ArgNameTerm f) (ArgClassTerm (Pi (bind (y, Embed t1) t2) Plus), Value)) . (withVar (ArgNameTerm x) (t1, Value))) (compType t)
      if aeq t2 theType then return (Pi (bind (y, Embed t1) t2) Plus) else typeError $ disp("Expected:") <+>disp (t2)<+>disp("Actually get:")<+> disp theType

-- | Term_let, a simple version 

compType (TermLetTerm1 b t) = do 
  (x, t1) <- unbind b
  theType <- compType t
  (withVar (ArgNameTerm x) (ArgClassTerm theType, NonValue)) (compType t1)

compType (TermLetProof b p) = do 
  (x, t1) <- unbind b
  thePred <- compPred p
  (withVar (ArgNameProof x) (ArgClassPredicate thePred, NonValue)) (compType t1)

-- | Term_case

compType (TermCase1 t branches) = do 
  theType <- compType t
  checkBranch Undefined theType branches

-- | Term_conv
compType (Conv t p binding) = do 
  t' <- compType t
  (Equal t1 t2) <- compPred p >>= ensureEqual
  (n, t) <- unbind binding
  if aeq (subst n t1 t) t' then do
                          compType (subst n t2 t) >>= ensureType
                          return (subst n t2 t) else typeError $ disp ("Expected:") <+> disp t' <+> disp ("Actually get:") <+> disp (subst n t1 t)


--   let n = zipWith ls t1;
--       n' = zipWith ls t2
--   if aeq (substs n t) t' then do
--                           compType (substs n' t) >>= ensureType
--                           return (substs n' t) else typeError $ disp ("Expected:") <+> disp t' <+> disp ("Actually get:") <+> disp (substs n t)


-- zipWith :: [Name Term] -> Term -> [(Name Term, Term)]      
-- zipWith [] _ =  []
-- zipWith (l:cs) t = (l,t):(zipWith cs t)

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

getInstance constrType [] = return constrType
getInstance _ _ = typeError $ disp("error from the use of getInstance.")
        

--calculate the local context for each branch

--calcLocalContext :: Term -> Scheme -> LocalEnv (Either String Bool)
--calcLocalContext ((TermVar c):[]) _ = return $ Right True

calcLocalContext constrType@(Pi b st) (h:ls)  = do  
  env <- get  
  ((argname, Embed argclass), t) <- unbind b
  put ((M.insert h (argclass, NonValue) (fst env)), snd env)
  calcLocalContext t ls 

calcLocalContext (TermVar _ ) [] = return $ True
calcLocalContext (TermApplication _ _ _ ) [] = return $ True
calcLocalContext (Pos _ t) ls = calcLocalContext t ls 
calcLocalContext _ _ = typeError $ disp ("Patterns variables doesn't fit well with the constructor.")
    
sanityCheck :: Term -> [ArgName] -> Bool
sanityCheck t (argname:cs) = case argname of
                               ArgNameTerm tm -> (elem tm (fv t)) || (sanityCheck t cs) 
                               ArgNameProof pr -> (elem pr (fv t)) || (sanityCheck t cs) 
                               ArgNamePredicate pred -> (elem pred (fv t)) || (sanityCheck t cs)
sanityCheck t [] = False

-- The type of the whole case expression, the type of t in case t, branches. 
checkBranch :: Term -> Term -> TermBranches -> TCMonad Term
checkBranch state theType ((constr, binding): l) = do
  ls <- flatten theType 
  (tuples,t1) <- unbind binding
  let argnames =  Prelude.map fst tuples
  ctype <- getClass (ArgNameTerm (string2Name constr)) >>= ensureArgClassTerm
  d' <- flatten ctype 
  if aeq (head d') (head ls) then 
      do theType' <- getInstance ctype (tail ls)
         case runIdentity(runErrorT (runFreshMT (execStateT (calcLocalContext theType' argnames) (M.empty, M.empty)))) of
           Left e -> throwError e
           Right env -> do
             t1' <- local (mapFst(M.union (fst env))) (compType t1) 
             if not (sanityCheck t1' argnames) then  
                 if aeq state Undefined then checkBranch t1' theType l else if aeq t1' state then checkBranch t1' theType l else typeError $ disp("Expected type:")<+>disp(state)<+>disp("Actual type:")<+>disp(t1') else typeError $ disp("An insane event just happened.") else typeError $ disp("The actual type of the datatype constructor") <+>disp(constr)<+> disp (" doesn't fit the corresponding datatype")<+>disp(head ls)
                   
checkBranch state theType [] = return $ state

typechecker :: Module -> Env Doc

typechecker [] = return $ disp "Type checker seems to approve your program, so congratulation!"

typechecker ((DeclData d):l) = do  
  checkData d
  typechecker l

typechecker ((DeclProgdecl p):l) = do 
  checkProgDecl p
  typechecker l

typechecker ((DeclProgdef p):l) = do  
  checkProgDef p
  typechecker l

typechecker ((DeclLogic p):l) = do  
  checkProofDecl p
  typechecker l

typechecker ((DeclProof p):l) = do  
  checkProofDef p
  typechecker l


-- type-check data type declaration
-- Append a tele in front of a term
teleArrow :: Tele -> Term -> Term
teleArrow Empty end = end
teleArrow (TCons binding) end = Pi (bind (argname,argclass) arrRest) stage
 where ((argname,stage,argclass),rest) = unrebind binding
       arrRest = teleArrow rest end

flatten :: MonadError TypeError m => Term -> m [Arg]

flatten (Pi b stage) = 
  let (b1, t1) = unsafeUnbind b in
  flatten t1

flatten (TermApplication t (ArgTerm t') st) = do
  ls <- flatten t
  ls' <- flatten t'
  return (ls++ls')
flatten (TermApplication t nonargterm st) = do
  ls <- flatten t
  return (ls++[nonargterm])
  
flatten (TermVar t) = return [ArgTerm (TermVar t)]

flatten (Pos _ t) = flatten t

flatten _ = typeError $ disp( "Not a standard form.")

checkData :: Datatypedecl -> Env Doc
checkData (Datatypedecl dataname bindings) = do
  (tele, cs) <- unbind bindings
  env <- get
  let datatype = teleArrow tele (Type 0) 
  case runIdentity (runErrorT (runFreshMT (runReaderT (runTCMonad (compType datatype)) env)))  of
    Left e -> throwError e
    Right t -> ensureType t
  put (M.insert (ArgNameTerm (string2Name dataname)) (ArgClassTerm datatype, Value) (fst env), snd env)
  checkConstructors dataname tele cs


--compare :: Monad M => [Arg] -> Tele -> M Bool
--compare the order of [arg] and Tele
compare [] Empty = return $ True
compare (h:l) (TCons bindings) =
  let ((argname,stage ,argclass),res) = unrebind bindings in
      case argname of
        ArgNameTerm u ->
            case h of
              ArgTerm (TermVar x) ->  
                 if aeq x u then compare l res else typeError $ disp ("error")
              _ -> typeError $ disp ("error")
        ArgNameProof u ->
                  case h of
                    ArgProof (ProofVar x) ->  
                        if aeq x u then compare l res else typeError $ disp ("error")
                    _ -> typeError $ disp ("error")
        ArgNamePredicate u ->
            case h of
              ArgPredicate (PredicateVar x) ->  
                  if aeq x u then compare l res else typeError $ disp ("error")
              _ -> typeError $ disp ("error")

compare _ _ = typeError $ disp("error")

checkConstructors :: String -> Tele -> [(String, Term)] -> Env Doc

checkConstructors dataname _ [] = return $ disp ("checked") <+> disp dataname
checkConstructors dataname tele ((constr,t2):l) = do 
  env <- get
  ls <- flatten t2 
  if aeq (head ls) (ArgTerm (TermVar (string2Name dataname))) then
      let t2' = teleArrow tele t2 in  
      do compare (tail ls) tele
         case runIdentity (runErrorT (runFreshMT (runReaderT (runTCMonad (compType t2')) env))) of
           Left e -> throwError e
           Right t -> ensureType t
         put ((M.insert (ArgNameTerm (string2Name constr))  (ArgClassTerm t2', Value)) (fst env),snd env )
         checkConstructors dataname tele l  else typeError $ disp("The type of the data constructor")<+>disp(constr)<+> disp("is not well-formed.") 

-- type-check program declaration

checkProgDecl :: Progdecl -> Env Doc
checkProgDecl (Progdecl t t') = do
  env <- get
  case t of
    TermVar x -> do 
     case runIdentity (runErrorT (runFreshMT (runReaderT (runTCMonad (compType t')) env))) of 
       Left e -> throwError e
       Right t -> ensureType t
     put ((M.insert (ArgNameTerm x)  (ArgClassTerm t', NonValue)) (fst env), snd env)
     return $ disp("Checked declaration of")<+> disp t
    _ -> typeError $ disp ("Unexpected term")<+> disp t

-- type-check program definition
checkProgDef :: Progdef -> Env Doc
checkProgDef (Progdef t t') = do
  env <- get
  case t of
    TermVar x ->  do
      case runIdentity (runErrorT (runFreshMT (runReaderT (runTCMonad (compType t')) env))) of
        Left e -> throwError e
        Right t'' -> do
          case runIdentity (runErrorT(runFreshMT (runReaderT (runTCMonad (getClass (ArgNameTerm x))) env))) of 
            Left e -> throwError e
            Right t1' -> do                         
              t1 <- ensureArgClassTerm t1'
              if aeq t1 t'' then do
                              put (fst env, M.insert (ArgNameTerm x) (ArgTerm t') (snd env) )
                              return $ disp ("Checked definition of") <+> disp t else typeError $ disp("Expecting")<+>disp(t1)<+>disp("Actually get:")<+>disp(t'') 
    _ -> typeError $ disp("Unexpected term")<+>disp t

checkProofDecl :: Logicdecl -> Env Doc
checkProofDecl (Logicdecl p pred) = do
  env <- get
  case p of
    ProofVar x -> do 
     case runIdentity (runErrorT (runFreshMT (runReaderT (runTCMonad (compLK pred)) env))) of 
       Left e -> throwError e
       Right lk -> case runIdentity (runErrorT (runFreshMT (runReaderT (runTCMonad (compSK lk)) env ))) of
                     Left e -> throwError e
                     Right k -> do
                       put ((M.insert (ArgNameProof x)  (ArgClassPredicate pred, NonValue)) (fst env), snd env)
                       return $ disp("Checked declaration of")<+> disp p
    _ -> typeError $ disp ("Unexpected proof")<+> disp p

checkProofDef :: Proofdef -> Env Doc
checkProofDef (Proofdef p p') = do
  env <- get
  case p of
    ProofVar x ->  do
      case runIdentity (runErrorT (runFreshMT (runReaderT (runTCMonad (compPred p')) env))) of
        Left e -> throwError e
        Right p'' -> do
          case runIdentity (runErrorT(runFreshMT (runReaderT (runTCMonad (getClass (ArgNameProof x))) env))) of 
            Left e -> throwError e
            Right p1' -> do                         
              p1 <- ensureArgClassPred p1'
              if aeq p1 p'' then do
                              put (fst env, M.insert (ArgNameProof x) (ArgProof p') (snd env) )
                              return $ disp ("Checked definition of") <+> disp p else typeError $ disp("Expecting1")<+>disp(p1)<+>disp("Actually get:")<+>disp(p'') 
    _ -> typeError $ disp("Unexpected proof")<+>disp p

