{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
  NamedFieldPuns #-}
module Language.SepPP.TypeCheck where

import Language.SepPP.Syntax
import Language.SepPP.PrettyPrint

import Unbound.LocallyNameless hiding (Con,isTerm,Val,join)
import Unbound.LocallyNameless.Ops(unsafeUnbind)

import Text.PrettyPrint

import Data.Typeable
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)
import Control.Exception(Exception)
import Control.Applicative
import Text.Parsec.Pos


-- * The typechecking monad

newtype TCMonad a =
  TCMonad { runTCMonad :: ReaderT Env (FreshMT (ErrorT TypeError IO)) a }
  deriving (Fresh, Functor, Monad, MonadReader Env, MonadError TypeError, MonadIO)


typecheck :: Module -> IO (Either TypeError ())
typecheck mod = do
  runErrorT $ runFreshMT $ runReaderT (runTCMonad (typecheckModule mod)) emptyEnv

-- ** The Environment
data EscapeContext = LeftContext | RightContext | StrictContext | NoContext
withEscapeContext c = local (\env -> env { escapeContext = c })

-- The typing context contains a mapping from variable names to types, with
-- an additional boolean indicating if it the variable is a value.
data Env = Env { gamma :: [(TName,(Term,Bool))]
               , sigma :: [()]
               , escapeContext :: EscapeContext }
emptyEnv = Env {gamma = [], sigma = [], escapeContext = NoContext}



-- | Add a new binding to an environment
extendEnv n ty isVal  e@(Env {gamma}) = e{gamma = (n,(ty,isVal)):gamma}


-- Functions for working in the environment
lookupBinding :: TName -> TCMonad (Term,Bool)
lookupBinding n = do
  env <- asks gamma
  maybe (err $ "Can't find variable " ++ show n ++ "\n" ++ show env) return (lookup n env)
extendBinding :: TName -> Term -> Bool -> TCMonad a -> TCMonad a
extendBinding n ty isVal m = do
  local (extendEnv n ty isVal) m


-- ** Error handling

data TypeError = ErrMsg [(SourcePos,Term)] String deriving (Show,Typeable)

instance Error TypeError where
  strMsg s = ErrMsg [] s
  noMsg = strMsg "<unknown>"


instance Exception TypeError

instance Disp TypeError where
  disp (ErrMsg [] msg) = return
          (nest 2 (text "Type Error" $$
              text msg))

  disp (ErrMsg ps msg) = return
     (start $$
      nest 2 (text "Type Error" $$
              text msg))
    where (p,t) = last ps
          start = text (show p)



addErrorPos p t (ErrMsg ps msg) = throwError (ErrMsg ((p,t):ps) msg)

err msg = throwError (strMsg msg)


-- * Running the typechecker.

-- | Typecheck an entire module
typecheckModule (Module n decls) = do
  checkDefs decls
  liftIO $ putStrLn "Typecheck passed"
  return ()


data DefRes = DataResult TName Term [(TName,Term)]
            | ProofResult TName Term Bool
            | ProgResult TName Term Bool

-- | Typecheck a single definition
checkDef (ProofDecl nm theorem proof) = do
  lk <- predSynth theorem
  isLK <- lkJudgment lk
  unless isLK $
         err $ "Theorem is not a well-formed logical kind " ++ show nm

  proofAnalysis proof theorem
  return $ ProofResult nm theorem False

checkDef (ProgDecl nm ty prog) = do
  typeAnalysis ty Type
  typeAnalysis prog ty
  return $ ProgResult nm ty False

checkDef (DataDecl (Con nm) ty cs) = do
  ran <- arrowRange ty
  unless (ran `aeq` Type) $
         err $ "The datatype decl " ++ show nm ++
               " must have range Type."

  -- Make sure that the type constructor is a well-formed type.
  typeAnalysis ty Type

  conTypes <- extendBinding nm ty True $
              mapM chkConstructor cs


  return (DataResult nm Type conTypes)


  where arrowRange (Pi _ binding) = do
          ((n,_),body) <- unbind binding
          arrowRange body
        arrowRange (Pos _ t) = arrowRange t
        arrowRange (Parens t) = arrowRange t
        arrowRange ty = return ty

        appHead (App t0 _ _) = appHead t0
        appHead (Parens t) = appHead t
        appHead (Pos _ t) = appHead t
        appHead t = t


        chkConstructor (c,ty) = do
           typeAnalysis ty Type
           ran <- arrowRange ty
           case appHead ran of
             Con tc -> do
               unless (tc == nm) $
                  err $ "In constructor " ++ show c ++
                        " result type does not match declared data type."
               return (c,ty)
             h -> do
               hd <- disp h
               err $ "Constructor head is " ++ render hd


checkDefs [] = return ()
checkDefs (d:ds) = do
  d <- checkDef d
  extendBinding' d (checkDefs ds)

  where extendBinding' (ProofResult n ty v) comp = extendBinding n ty v comp
        extendBinding' (ProgResult n ty v) comp = extendBinding n ty v comp
        extendBinding' (DataResult n ty cs) comp =
          extendBinding n ty True $
                        foldr (\(n,ty) m -> extendBinding n ty True m) comp cs




-- The S, G |- val t judgement.
valJudgment (Var v) = do
  (_,v) <- lookupBinding v
  return v
valJudgment Type = return True
valJudgment (Pi _ _ ) = return True
valJudgment (Lambda _ _ _ ) = return True
valJudgment (Rec _ ) = return True
-- valJudgement Nat = True
valJudgment t@(App _ _ _ ) =
  case splitApp t of
    ((Con _):args) -> do
       vals <- mapM valJudgment args
       return $ and vals
    _ -> return False


-- * Judgements on proof fragment

-- The S,G |- LK : LogicalKind judgment
lkJudgment (Formula _ ) = return True
lkJudgment (Forall binding) = do
  ((n,Embed ty),body) <- unbind binding
  unless (isA ty)$
    err "Expecting the classifier for a logical kind argument to be syntax class 'A'"
  extendBinding n ty False (lkJudgment body)

guardLK t = do
  lk <- lkJudgment t
  td <- disp t
  unless lk $ err $ render td ++ " is not a valid logical kind."


-- The S,G |- P : LK judgment
predSynth (Parens p) = predSynth p
predSynth (Pos p t) = predSynth t `catchError` addErrorPos p t
predSynth (Forall binding) = do
  ((n,Embed t),body) <- unbind binding
  -- We need to do a syntactic case-split on ty. Going to use backtracking for now.
  case down t of
    Formula i -> do  -- Pred_Forall3 rule
           form <- extendBinding n t False (predSynth body)
           (Formula j) <- guardFormula form
           return (Formula (max (i+1) j))
    (Forall binding') -> do -- Pred_Forall4 rule
           guardLK t
           form <- extendBinding n t False (predSynth body)
           guardFormula form
    _ -> do
      -- TODO: Handle the case where the type is a pred.

      -- * ty is a term or pred. just handling term for now
      ty <- typeSynth t
      dty <- disp ty
      unless (ty `aeq` Type) $
             err $ "Expecting a type for " ++ render dty


      form <- extendBinding n t False (predSynth body)
      guardFormula form



  where guardFormula t@(Formula i) = return t
        guardFormula _ = err "Not a formula"


predSynth (Equal t0 t1) = do -- Pred_K_Eq rule
  ty0 <- typeSynth t0
  ty1 <- typeSynth t1
  -- TODO: Do we need to check to see that ty0 and t1 : Type?
  return (Formula 0)

predSynth (Terminates t) = do -- Pred_Terminates rule
  typeSynth t
  return (Formula 0) -- TODO: Should this really be 0?

predSynth (Lambda Form Static binding) = do -- Pred_Lam rule
  ((n,Embed ty),body) <- unbind binding
  -- First Premise
  unless (isW ty) $
         err $ show ty ++ " is not in the 'W' syntactic class."
  -- Second Premise
  form <- extendBinding n ty False (predSynth body)
  lk <- lkJudgment form
  dform <- disp form
  unless lk $ err (render dform ++ " is not a valid logical kind.")

  return (Forall (bind (n,Embed ty) form))


predSynth (App t0 Static t1) = do -- Pred_App rule
  form <- predSynth t0
  case form of
    Forall binding -> do
              ((n,Embed ty),body) <- unbind binding
              guardLK body
              typeAnalysis t1 ty
              return $ subst n t1 body
    _ -> do
      d0 <- disp t0
      err ("Can't apply non-quantified predicate " ++ render d0)


predSynth p = do
  d <- disp p
  err $ render d ++ " is not a valid predicate."

proofSynth (Pos p t) = proofSynth t `catchError` addErrorPos p t

proofSynth (Var x) = do         -- Prf_Var
  (ty,_) <- lookupBinding x
  requireA ty
  pty <- predSynth ty
  requireQ pty
  return ty

-- TODO: Waiting for Harley to split the forall rule before implementing it.
proofSynth (App p Static b) = do
  pty <- predSynth p
  case pty of
    Forall binding -> do
             ((n,Embed ty),body) <- unbind binding
             requireB ty
             requirePred body
             bty <- bAnalysis b ty
             return $ subst n b body

proofSynth (Parens p) = proofSynth p
proofSynth (Ann p pred) = do
  proofAnalysis p pred
  return pred

proofSynth (ConvCtx p ctx) = do
  l <- copy LeftContext ctx
  lty <- withEscapeContext LeftContext $ predSynth l
  proofAnalysis p l
  r <- copy RightContext ctx
  rty <- withEscapeContext RightContext $ predSynth r
  return r

proofSynth (Sym t) = do
  ty <- proofSynth  t
  case down ty of
     (Equal t1 t0)-> return (Equal t0 t1)
     _  ->
       throwError $ strMsg "Sym's argument must have the type of an equality proof"



proofSynth t = do
  dt <- disp t
  err $ "TODO: proofSynth: " ++ render dt

proofAnalysis t (Pos p ty) = proofAnalysis t ty
proofAnalysis (Pos p t) ty = proofAnalysis t ty `catchError` addErrorPos p t
-- FIXME: This is a stopgap, while waiting on the new split rules for
-- Prf_Forall.  FIXME: The static/dynamic argument should always be static
-- (since this is a proof) but the concrete syntax doesn't handle this right, it
-- always requires static/dynamic annotations, even if
proofAnalysis (Lambda Form _ pfBinding)
              out@(Forall predBinding) = do -- Prf_Forall.

  Just ((proofName,Embed pfTy),pfBody,(predName,Embed predTy),predBody) <-
    unbind2  pfBinding predBinding
  -- ((predName,Embed predTy),predBody) <- unbind predBinding

  -- unless (pfTy `aeq` predTy  && proofName == predName) $
  --        err "PA domerr"

  --sort <- getSort pfTy
  pfKind <- typeSynth pfTy
  requireQ pfKind

  -- Whether the var should be marked value or not is sort of up in the air...
  extendBinding proofName pfTy False (proofAnalysis pfBody predBody)
  return out


proofAnalysis (Parens p) eq = proofAnalysis p eq
proofAnalysis p (Parens eq) = proofAnalysis p eq
proofAnalysis (Join _ _) eq@(Equal t0 t1) = do
  typeSynth t0
  typeSynth t1
  -- FIXME: Need to define operational semantics.
  join t0 t1
  return eq

-- FIXME: check to see that ty and ty' are alpha-equivalent
proofAnalysis (Ann t ty') ty = proofAnalysis t ty

proofAnalysis (TerminationCase s binding) ty = do
  dty <- disp ty
  liftIO $ putStrLn $ "looking for " ++ render dty
  sty <- typeSynth s
  (w,(abort,terminates)) <- unbind binding
  extendBinding w (Equal (Abort sty) s) True (proofAnalysis abort ty)
  extendBinding w (Terminates s) True (proofAnalysis terminates ty)
  return ty

proofAnalysis (Strict c) ty = withEscapeContext StrictContext $ do
  cty <- typeSynth c
  case isStrictContext c of
    Nothing -> throwError $ strMsg "Not a strict context"
    Just (e,f) -> do
      eqTy <- typeSynth e
      case down eqTy of
        (Equal (Abort t) e2) -> do
           let ty' = Equal (Abort t) (f e2)
           dty' <- disp ty'
           dty <- disp ty
           unless  (ty' `aeq` ty) $
                   err $ "In strict, actual type " ++ render dty' ++
                         " does not match expected type " ++ render dty
           return ty
        _ -> throwError $ strMsg
               "In strict, the context hole is not of the proper form abort = e"


proofAnalysis (ConvCtx p ctx) ty = do
  l <- copy LeftContext ctx
  lty <- withEscapeContext LeftContext $ predSynth l
  proofAnalysis p l
  r <- copy RightContext ctx
  rty <- withEscapeContext RightContext $ predSynth r
  unless (ty `aeq` r) $ do
    dty <- disp ty
    dr <- disp r
    throwError $ strMsg $ "RHS of conv " ++ render dr ++ " does not match " ++
               "expected type " ++ render dty

  return r



proofAnalysis (Sym t) ty@(Equal t0 t1) = do
  proofAnalysis t (Equal t1 t0)
  return ty


proofAnalysis proof pred = do
  d <- disp (Ann proof pred)
  err $ "TODO: proofAnalysis: " ++ render d



-- * Judgements on program fragment
typeSynth (Pos p t) = typeSynth t `catchError` addErrorPos p t
typeSynth (Parens t) = typeSynth t
typeSynth Type = return Type
typeSynth (Var n) = do
  (ty,_) <- lookupBinding n
  return ty
typeSynth (Con n) = do
  (ty,_) <- lookupBinding n
  return ty



typeSynth (App t0 stage t1) = do
  ty0 <- typeSynth t0
  case down ty0 of
    Pi piStage binding -> do

             unless (piStage == stage) $ do
              err $ "Stage " ++ show piStage ++  " for arrow " ++
                    "does not match stage for application " ++ show stage

             ((x,Embed dom),body) <- unbind binding
             argTy <- typeAnalysis t1 dom
             requireA argTy
             require_a t1
             let sub = subst x t1 body
             return sub


    _ -> do
      dt0 <- disp t0
      dty0 <- disp ty0
      err $ "Can't apply a term " ++ render dt0 ++
               " with type " ++ render dty0

typeSynth (Escape t) = do
  escctx <- asks escapeContext
  case escctx of
    NoContext -> throwError $ strMsg "Can't have an escape outside of a context."
    LeftContext -> do
       ty <- typeSynth t
       case down ty of
         (Equal l _) -> return l
         _ -> throwError $ strMsg "Can't cast by something not an equality proof."

    RightContext -> do
       ty <- typeSynth t
       case down ty of
         (Equal _ r) -> return r
         _ -> throwError $ strMsg "Can't cast by something not an equality proof."
    StrictContext -> do
      ty <- typeSynth t
      dty <- disp ty
      dt <- disp t
      liftIO $ putStrLn $ "ty is " ++ render dty ++ "\n ++ t is " ++ render dt
      case down ty of
        Equal (Abort _) e -> return e -- typeSynth e
        _ -> do
          dty <- disp ty
          throwError $
               strMsg $ "In strict context, witness of abort" ++
                      render dty ++ " equality is ill-formed."

typeSynth (ConvCtx t ctx) = do
  l <- copy LeftContext ctx
  lty <- withEscapeContext LeftContext $ typeSynth l
  proofAnalysis t l
  r <- copy RightContext ctx
  rty <- withEscapeContext RightContext $ typeSynth r
  return r


typeSynth (Ann t ty) = do
  typeAnalysis t ty
  return ty

typeSynth (Abort t) = do
  typeAnalysis t Type
  return t

typeSynth t = err $ "TODO: typeSynth: " ++ show t

typeAnalysis t (Pos p ty) = typeAnalysis t ty
typeAnalysis (Pos p t) ty =
  typeAnalysis t ty `catchError` addErrorPos p t
typeAnalysis Type Type = return Type -- Term_Type
typeAnalysis (Pi _ binding) Type = do -- Term_Pi
  ((n,Embed ty),body) <- unbind binding
  extendBinding n ty False $ typeAnalysis body Type

typeAnalysis (Ann t ty) ty' = do
  typeAnalysis t ty'
  unless (ty `aeq` ty') $
         err "Ascribed type does not match required type."
  return ty

typeAnalysis (Con t) ty = do -- Term_Var
  (ty',_) <- lookupBinding t
  unless (ty' `aeq` ty) $
         err $ "Constructor " ++ show t ++ " has type " ++ show ty'  ++ ", whichdoesn't match expected type " ++ show ty

  return ty


typeAnalysis (Rec progBinding) res@(Pi Dynamic piBinding) = do -- Term_Rec
  -- FIXME: This is a hack, because there are different number of binders in the
  -- Rec and Pi forms.
  (p1@(f,_),body) <- unbind progBinding
  (p2,piBody) <- unbind piBinding
  Just ((f,(arg,Embed ty)),body,(_,(piArg,Embed piTy)),piBody)
    <- unbind2 (bind p1 body) (bind (f,p2) piBody)

  dty <- disp ty
  dPiTy <- disp piTy
  unless (ty `aeq` piTy) $
         err $ "Type " ++ render dty ++ " ascribed to lambda bound variable " ++
               " does not match type " ++ render dPiTy ++
               " ascribed to pi-bound variable."

  extendBinding f res True $
    extendBinding arg ty True $ typeAnalysis body piBody
  return res



typeAnalysis (Lambda Program progStage progBinding) ty@(Pi piStage piBinding) = do
  unless (progStage == piStage) $
         err $ "Lambda stage annotation " ++ show progStage ++ " does not " ++
               "match arrow annotation " ++ show piStage



  ((progName,Embed progTy), progBody) <- unbind progBinding
  ((piName,Embed piTy), piBody) <- unbind piBinding

  -- TODO: Several side conditions on stage annotations
  extendBinding progName progTy True $ typeAnalysis progBody piBody

typeAnalysis (Case s binding) res = do
  ((eqName,termProof),alts) <- unbind binding
  unless (termProof == Nothing) $
    err "Can't introduce termination proof in a programmatic case-split."
  sTy <- typeSynth s
  return res

typeAnalysis (App t0 stage t1) ty = do
  ty0 <- typeSynth t0

  -- FIXME: Do something with the stage.

  case down ty0 of
    Pi piStage binding -> do
             unless (piStage == stage) $ do
              err $ "Stage " ++ show piStage ++  " for arrow " ++
                    "does not match stage for application " ++ show stage

             ((x,Embed dom),body) <- unbind binding
             argTy <- typeAnalysis t1 dom
             requireA argTy
             require_a t1
             let sub = subst x t1 body
             dsub <- disp sub
             dty <- disp ty
             unless (sub `aeq` ty) $ err $
                    "Actual type " ++ render dsub ++
                    " does not match expected type " ++
                    render dty
             return ty


    _ -> err $ "Can't apply a term " ++ show t0 ++
               " with type " ++ show ty0


typeAnalysis tm@(Var x) ty = do
  ty' <- typeSynth tm
  unless (ty `aeq` ty') $ do
    dx <- disp x
    dty' <- disp ty'
    dty <- disp ty
    err $ "Variable " ++ render dx ++ " has type '" ++ render dty' ++
          "' but type '" ++ render dty ++ "' was expected."
  return ty


typeAnalysis (Escape t) ty = do
  ty <- typeSynth t
  dty <- disp ty
  dt <- disp t
  liftIO $ putStrLn $ "ty is " ++ render dty ++ "\n ++ t is " ++ render dt
  escctx <- asks escapeContext
  case escctx of
    NoContext -> throwError $ strMsg "Can't have an escape outside of a context."
    LeftContext -> throwError $ strMsg "Wait for it"
    RightContext -> throwError $ strMsg "Wait for it"
    StrictContext -> do
      ty <- typeSynth t
      case down ty of
        Equal (Abort _) e -> return e -- typeAnalysis e ty
        _ -> do
          dty <- disp ty
          throwError $
               strMsg $ "In strict context, witness of abort" ++
                      render dty ++ " equality is ill-formed."




typeAnalysis (ConvCtx t ctx) ty = do
  l <- copy LeftContext ctx
  lty <- withEscapeContext LeftContext $ typeSynth l
  proofAnalysis t l
  r <- copy RightContext ctx
  rty <- withEscapeContext RightContext $ typeSynth r

  unless (ty `aeq` r) $ do
    dty <- disp ty
    dr <- disp r
    throwError $ strMsg $ "RHS of conv " ++ render dr ++ " does not match " ++
               "expected type " ++ render dty
  return r




typeAnalysis t ty = err $ "TODO: typeAnalysis" ++ show t ++ "\n" ++ show ty


-- FIXME: This needs to try to synthesize (analyze) a type for everything in the b
-- syntactic class, not just terms.
bSynth t = typeSynth t
bAnalysis t = typeAnalysis t


-- Syntactic class predicates (TODO)
isA t = isTerm t || isPred t
isB t = isTerm t || isPred t || isLK t

-- isB t = do
--   c <- getClassification t
--   return $ c `elem` [SortType

isW Type = True
isW (Formula _) = True
isW (Pos _ t) = isW t
isW (Parens t) = isW t

isW _ = False

isQ Type = True
isQ (Formula _) = True
isQ (Pos _ t) = isQ t
isQ (Parens t) = isQ t
isQ t = isLK t

isLK (Pos _ t) = isLK t
isLK (Formula _) = True
isLK (Forall binding) = isA ty && isLK body
  where ((n,Embed ty),body) = unsafeUnbind binding
isLK _ = False


isPred (Var x) = True
isPred (Lambda Form Static binding) = isA ty && isPred body
  where ((n,Embed ty),body) = unsafeUnbind binding
isPred (App t0 Static t1) = isPred t0 && is_a t1
isPred (Forall binding) = isB ty && isPred body
  where ((n,Embed ty),body) = unsafeUnbind binding
isPred (Equal t0 t1) = isTerm t0 && isTerm t1
isPred (IndLT t0 t1) = isTerm t0 && isTerm t1
isPred (Terminates t) = isTerm t
isPred (Ann p t) = isPred p && isLK t
isPred (Parens p) = isPred p
isPred (Pos _ t) = isPred t
isPred _ = False


isProof (Var x) = True
isProof (Lambda Form  Static binding) = isB ty && isProof body
  where ((n,Embed ty),body) = unsafeUnbind binding
isProof (App t0 Static t1) = isProof t0 && is_b t1
isProof (Join _ _) = True
isProof (Conv p ps binding) = isProof p &&
                              and [is_q t | t <- ps] &&
                              is_a body
  where (_,body) = unsafeUnbind binding
isProof (Val t) = isTerm t
isProof (Ord t0) = isTerm t0
isProof (Case scrutinee binding) =
  isTerm scrutinee && ok
 where chkAlt a = let ((c,as),alt) = unsafeUnbind a in isProof alt
       ok = case unsafeUnbind binding of
              ((cpf,Just tpf),alts) -> and (map chkAlt alts)
              _ -> False

isProof (TerminationCase scrutinee binding) =
    isTerm scrutinee && isProof p0 && isProof p1
  where (pf,(p0,p1)) = unsafeUnbind binding

isProof (Ind binding) = isTerm ty &&  isProof body
  where ((f,(n,Embed ty),opf),body) = unsafeUnbind binding
isProof (Contra p) = isProof p
isProof (ContraAbort p0 p1) = isProof p0 && isProof p1
isProof (Ann p pred) = isProof p && isPred pred
isProof (Parens p) = isProof p
isProof (Pos _ t) = isProof t
isProof t = False



isTerm (Var _) = True
isTerm (Con _) = True
isTerm Type = True
isTerm (Pi _ binding) = isA ty && isTerm body
  where ((n,Embed ty),body) = unsafeUnbind binding
isTerm (Lambda Program _ binding) = isA ty && isTerm body
  where ((n,Embed ty),body) = unsafeUnbind binding
isTerm (Conv t ts binding) = isTerm t &&
                             and [is_q t | t <- ts] &&
                             isTerm body
  where (_,body) = unsafeUnbind binding
isTerm (App t0 _ t1) = isTerm t0 && is_a t1
isTerm (Abort t) = isTerm t
isTerm (Rec binding) = isTerm ty &&  isTerm body
  where ((f,(n,Embed ty)),body) = unsafeUnbind binding
isTerm (Ann t0 t1) = isTerm t0 && isTerm t1
isTerm (Parens t) = isTerm t
isTerm (Pos _ t) = isTerm t
isTerm (Escape t) = isTerm t
isTerm t = False


is_a t = isTerm t || isProof t || isLK t
is_b t = isTerm t || isProof t || isPred t

is_q (Equal t0 t1) = isTerm t0 && isTerm t1
is_q t = isProof t


-- Lifting predicates to the TC monad, where False == failure
requireA = require isA "A"
requireQ = require isQ "Q"
requireB = require isB "B"
requirePred = require isPred "P"
require_a = require is_a "a"


require p cls (Parens t) = require p cls t
require p cls (Pos _ t) = require p cls t
require p cls (Var n) = do
  (v,_) <- lookupBinding n
  require p cls v

require p cls t =
  unless (p t) $
         err $ show t ++ " is not the proper syntactic class (" ++
               cls ++ ")."



-- Placeholder for op. semantics
join t1 t2 = unless (t1 `aeq` t2) $ err "Terms not joinable"



down (Pos _ t) = down t
down (Parens t) = down t
down t = t

-- Get the classification of a classifier (Type,Predicate,LogicalKind)
data Sort = SortType | SortPred | SortLK deriving (Eq,Show)
getClassification (Pos _ t) = getClassification t
getClassification (Parens t) = getClassification t
getClassification t = do
  ta `comb` pa `comb` la `comb` end
  where ta = typeAnalysis t Type >> return SortType
        pa = do sort <- predSynth t
                unless (isLK (down sort)) $
                  throwError (strMsg "not a predicate")
                return SortPred
        la = do unless (isLK t) (throwError (strMsg "Could not classify classifier"))
                return SortLK
        comb a b = a `catchError` (\_ -> b)
        end = do dt <- disp t
                 throwError $ strMsg $ "Can't classify " ++ render dt




copy b (Equal l r) = do
  l' <- copy b l
  r' <- copy b r
  return $ Equal l' r'

copy b (App t0 s t1) = do
  t0' <- copy b t0
  t1' <- copy b t1
  return $ App t0' s t1'

copy b (Var x)  = return (Var x)
copy b (Con x)  = return (Con x)
copy b (Escape t) = do
  ty <- typeSynth t
  case down ty of
    (Equal l r) -> case b of
                     LeftContext -> return l
                     RightContext -> return r
                     _ -> throwError $ strMsg $ "Copy can't reach this."
    _ -> throwError $ strMsg $ "Can't escape to something not an equality"


copy b (Parens t) = Parens <$> copy b t
copy b (Pos p t) = Pos p <$>  copy b t
copy b t = error $ show t