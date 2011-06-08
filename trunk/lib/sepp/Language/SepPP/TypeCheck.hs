{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
  NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances #-}
module Language.SepPP.TypeCheck where

import Language.SepPP.Syntax
import Language.SepPP.PrettyPrint
import Language.SepPP.Eval
import Language.SepPP.TCUtils

import Unbound.LocallyNameless hiding (Con,isTerm,Val,join)
import Unbound.LocallyNameless.Ops(unsafeUnbind)

import Text.PrettyPrint

import Data.Typeable

import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)
import Control.Exception(Exception)
import Control.Applicative
import Text.Parsec.Pos



typecheck :: Module -> IO (Either TypeError ())
typecheck mod = do
  runErrorT $ runFreshMT $ runReaderT (runTCMonad (typecheckModule mod)) emptyEnv



-- * Running the typechecker.

-- | Typecheck an entire module
typecheckModule (Module n decls) = do
  checkDefs decls
  -- liftIO  $ putStrLn "Typecheck passed"
  return ()


data DefRes = DataResult TName Term [(TName,Term)]
            | ProofResult TName Term Term Bool
            | ProgResult TName Term Term Bool

-- | Typecheck a single definition
checkDef (ProofDecl nm theorem proof) = do
  lk <- predSynth theorem
  isLK <- lkJudgment lk
  ensure isLK ("Theorem is not a well-formed logical kind " <++> nm)

  proofAnalysis proof theorem
  return $ ProofResult nm theorem proof False

checkDef (ProgDecl nm ty prog) = do
  typeAnalysis ty Type
  typeAnalysis prog ty
  return $ ProgResult nm ty prog False

checkDef (DataDecl (Con nm) ty cs) = do
  ran <- arrowRange ty
  ty `expectType` Type

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
               ensure (tc == nm) $
                        "In constructor " <++> c <++>
                        "result type does not match declared data type."
               return (c,ty)
             h -> do
               die $ "Constructor head is" <++> h


checkDefs [] = return ()
checkDefs (d:ds) = do
  d <- checkDef d
  extendBinding' d (checkDefs ds)

  where extendBinding' (ProofResult n ty def v) comp =
          extendDefinition n ty def v comp
        extendBinding' (ProgResult n ty def v) comp =
          extendDefinition  n ty def v comp
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
  ensure (isA ty) $
    "Expecting the classifier for a logical kind argument to be syntax class"
    <++> "'A'."
  extendBinding n ty False (lkJudgment body)

guardLK t = do
  lk <- lkJudgment t
  ensure lk (t <++> "is nota valid logical kind.")


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

    dom -> do
      cls <- getClassification dom
      case cls of
        SortPred -> do  -- Pred_Forall1
          lk <- predSynth dom
          case lk of
            Formula i -> do
                    extendBinding n dom False (predSynth body)
            _ -> do
                err "predSynth pred case, not a formula."
        SortType -> do
                 ty <- typeSynth t
                 dty <- disp ty
                 -- unless (ty `aeq` Type) $
                 --      err $ "Expecting a type for " ++ render dty
                 ty `expectType` Type


                 form <- extendBinding n t False (predSynth body)
                 guardFormula form



  where guardFormula t@(Formula i) = return t
        guardFormula _ = err "Not a formula"


predSynth (Equal t0 t1) = do -- Pred_K_Eq rule
  ty0 <- typeSynth t0
  ty1 <- typeSynth t1
  -- TODO: Do we need to check to see that ty0 and t1 : Type?
  return (Formula 0)

predSynth (IndLT t0 t1) = do
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
  ensure (isW ty) $ ty <++> "is not in the 'W' syntactic class."
  -- Second Premise
  form <- extendBinding n ty False (predSynth body)
  lk <- lkJudgment form
  -- dform <- disp form
  -- unless lk $ err (render dform ++ " is not a valid logical kind.")
  ensure lk $ form <++> " is not a valid logical kind."

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
-- FIXME: The static/dynamic stage is not being respected here
proofSynth t@(App p _ b) = do
  pty <- proofSynth p
  case down pty of
    Forall binding -> do
             ((n,Embed ty),body) <- unbind binding
             requireB ty
             requirePred body
             bty <- bAnalysis b ty
             return $ subst n b body
    Pi stage binding  -> do
             ((n,Embed ty),body) <- unbind binding
             --requireB ty
             --requirePred body
             ensure (constrApp t) $ t <++> "is not a construction."
             bty <- typeAnalysis b ty
             return $ subst n b body

    _ -> die $ "proofSynth (App)" <++> t

  where constrApp (Con c) =  True
        constrApp (App f _ x) = (constrApp f)
        constrApp (Parens t) = constrApp t
        constrApp (Pos x t) = constrApp t
        constrApp _ = False


proofSynth (Parens p) = proofSynth p
proofSynth (Ann p pred) = do
  proofAnalysis p pred
  return pred

proofSynth (ConvCtx p ctx) = do
  l <- copyEqualInEsc LeftContext ctx
  lty <- withEscapeContext LeftContext $ predSynth l
  proofAnalysis p l
  r <- copyEqualInEsc RightContext ctx
  rty <- withEscapeContext RightContext $ predSynth r
  return r

proofSynth (Sym t) = do
  ty <- proofSynth  t
  case down ty of
     (Equal t1 t0)-> return (Equal t0 t1)
     _  ->
       err "Sym's argument must have the type of an equality proof."


proofSynth (Aborts c) = withEscapeContext StrictContext $ do
  cty <- typeSynth c
  case isStrictContext c of
    Nothing -> err "Not a strict context."
    Just (e,f) -> do
      eqTy <- typeSynth e
      case down eqTy of
        (Equal (Abort t) e2) -> do
           let ty' = Equal (Abort t) (f e2)
           return ty'
        _ -> err $ "In strict, the context hole is not of the proper form abort = e"

proofSynth (Con n) = do
  (ty,_) <- lookupBinding n
  return ty

proofSynth (t@(Val x)) =
  do let f t = do ty <- typeSynth t
                  case down ty of
                   (Terminates x) -> return x
                   _ -> throwError $ strMsg $ "Can't escape to something not a Termination in valCopy"
     term <- escCopy f x
     typeSynth term
     stub <- escCopy (\ x -> return Type) x
     b <- synValue stub
     if b
        then return(Terminates (down term))
        else  do d <- disp t
                 err $ "Non Value: " ++ render d


proofSynth (Equal t0 t1) = do
  k0 <- typeSynth t0
  typeAnalysis k0 Type
  k1 <- typeSynth t1
  typeAnalysis k1 Type
  return Type

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
proofAnalysis (Join lSteps rSteps) eq@(Equal t0 t1) = do
  typeSynth t0
  typeSynth t1
  -- FIXME: Need to define operational semantics.
  join lSteps rSteps t0 t1
  return eq

-- FIXME: check to see that ty and ty' are alpha-equivalent
proofAnalysis (Ann t ty') ty = do
  unless (ty `aeq` ty') $ do
    dty' <- disp ty'
    dty <- disp ty
    err $ "Annotated type " ++ render dty' ++ " doesn't match " ++
        render dty
  proofAnalysis t ty'
  return ty'


-- FIXME: Enforce the 'static' stage.
proofAnalysis (App p _ b) res = do
  pty <- proofSynth p
  case down pty of
    Forall binding -> do
             ((n,Embed ty),body) <- unbind binding
             requireB ty
             requirePred body
             bty <- bAnalysis b ty
             let snb = subst n b body
             snb `expectType` res
             -- unless (snb `aeq` res) $
             --        err "proofAnalysis app: not the expected type"

             return snb
    Pi Static binding -> do
             ((n,Embed ty),body) <- unbind binding
             requireB ty
             requirePred body
             bty <- bAnalysis b ty
             let snb = subst n b body
             unless (snb `aeq` res) $
                    err "proofAnalysis app: not the expected type"
             return snb
    (w@(Pi Dynamic b)) ->
           do d <- disp p
              t <- disp w
              err ("function in proof application: "++render d++"\nhas a dynamic function type: "++render t)

    rng -> do d <- disp p
              t <- disp rng
              err ("function in application: "++render d++"\ndoes not have a function type: "++render t)


proofAnalysis (TerminationCase s binding) ty = do
  dty <- disp ty
  -- liftIO  $ putStrLn $ "looking for " ++ render dty
  sty <- typeSynth s
  (w,(abort,terminates)) <- unbind binding
  extendBinding w (Equal (Abort sty) s) True (proofAnalysis abort ty)
  extendBinding w (Terminates s) True (proofAnalysis terminates ty)
  return ty

proofAnalysis (Aborts c) ty = withEscapeContext StrictContext $ do
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
  l <- copyEqualInEsc LeftContext ctx
  lty <- withEscapeContext LeftContext $ predSynth l
  proofAnalysis p l
  r <- copyEqualInEsc RightContext ctx
  rty <- withEscapeContext RightContext $ predSynth r

  dr <- disp r
  dl <- disp l
  dty <- disp ty
  -- liftIO  $ putStrLn $ "ConvCtx expecting type " ++ render dty
  -- liftIO  $ putStrLn $ "ConvCtx LHS " ++ render dl
  -- liftIO  $ putStrLn $ "ConvCtx RHS " ++ render dr


  unless (ty `aeq` r) $ do
    dty <- disp ty
    dr <- disp r
    throwError $ strMsg $ "RHS of conv " ++ render dr ++ " does not match " ++
               "expected type " ++ render dty

  return r



proofAnalysis (Sym t) ty@(Equal t0 t1) = do
  proofAnalysis t (Equal t1 t0)
  return ty

-- res should have the form (\forall x:t1 . \forall u:x! . P)
proofAnalysis (Ind prfBinding) res@(Forall predBinding) = do -- Prf_Ind
  -- FIXME: This is a hack, because there are different number of binders in the
  -- Ind and Forall forms.
  let clean m = (\((n,Embed ty),t) -> ((n,Embed (down ty)),down t)) <$> m
  (p1@(fun,_,witness),_) <- unbind prfBinding
  (a1,Forall predBinding') <- clean $ unbind predBinding

  ((witness',Embed (Terminates x)),pred) <- clean $ unbind predBinding'

  Just ((f,(x,Embed t1), u),proofBody,(f',(x',Embed t1'), u'),predBody)
    <- unbind2 prfBinding (bind (fun,a1,witness') pred)

  -- TODO: Add a few more checks of consistency
  -- dty <- disp ty
  -- dPredTy <- disp predTy
  -- unless (ty `aeq` predTy) $
  --        err $ "Type " ++ render dty ++ " ascribed to lambda bound variable " ++
  --              " does not match type " ++ render dPredTy ++
  --              " ascribed to pi-bound variable."



  let xvar = Var x
      y = string2Name "y"
      yvar = Var y
  let fty = Forall (bind (y,Embed t1) -- FIXME: should take t2 as a parameter.
                           (Forall (bind (u,Embed (IndLT yvar xvar))
                                         (subst x yvar predBody))))
  extendBinding x t1 False $
   extendBinding u (Terminates xvar) True $
    extendBinding f fty True $ proofAnalysis proofBody predBody

  return res

proofAnalysis (Case s (Just termProof) binding) ty = do
    (sEq,alts) <- unbind binding
    typeSynth s
    sTermType <- proofSynth termProof
    unless (sTermType `aeq` Terminates s) $ do
         dTerm <- disp termProof
         ds <- disp (Terminates s)
         err $ render dTerm ++ " is not a proof of " ++ render ds

    mapM (altAnalysis sEq) alts
    return ty
  where altAnalysis eqpf alt = do
          -- FIXME: We need to make sure that constructors belong to the type of
          -- the scruinee, and that all cases are covered.
          ((cons,vars),body) <- unbind alt
          (ctype,_) <- lookupBinding (string2Name cons)
          dctype <- disp ctype
          let pat = foldl (\t0 t1 -> (App t0 Dynamic t1))
                      (Con (string2Name cons)) (map Var vars)

          dty <- disp ty
          dbody <- disp body
          -- liftIO  $ putStrLn $ "In alt, looking for type " ++ render dty
          -- liftIO  $ putStrLn $ " in body " ++ render dbody
          ty' <- substPat vars ctype $
                   extendBinding eqpf (Equal pat s) True  $ proofAnalysis body ty
          dty' <- disp ty
          -- liftIO  $ putStrLn $ "Result type of case alt is " ++ render dty'
          return dty'


        substPat [] ty m = m
        substPat (n:ns) ty m =
          case down ty of
            (Pi _ binding) -> do
             ((n',Embed ty),body) <- unbind binding
             extendBinding n ty True $ substPat ns body m



proofAnalysis (Let binding) ty = do
    ((n,pf,Embed t),body) <- unbind binding
    ty' <- proofSynth t
    -- what is the value annotation for this?
    extendBinding n ty' True $
     extendBinding pf (Equal (Var n) t) True $
      proofAnalysis body ty


proofAnalysis (Ord w) ty@(IndLT l r) = do
  -- Skeleton version of the 'ord' axiom.
  ty <- proofSynth w
  case down ty of
    (Equal l' r') -> do
        let (c,ls) = splitApp' l'
        -- let (cr,rs) = splitApp' r'
        -- unless (not (null ls) &&  or (map (aeq l) (tail ls))) $
        --    err $ "proofAnalysis (ord) sym error left " ++ show  ls  ++ "   \n right:" ++ show rs
        ensure (r `aeq` r' && any (aeq l) ls) $ "Ord error" <++> ty



        return ty


proofAnalysis t@(OrdTrans p1 p2) ty@(IndLT y x) = do
  ty1 <- proofSynth p1
  ty2 <- proofSynth p2
  case (down ty1,down ty2) of
    (IndLT y' z, IndLT z' x')
      | z `aeq` z' && y `aeq` y' && x `aeq` x' ->
          return ty
      | otherwise -> die $ "Bad ordtrans" <++> t <++> ty1 <++> ty2 <++> ty
    _ -> die $ "Bad ordtrans" <++> t <++> ty1 <++> ty2 <++> ty


proofAnalysis (Var n) ty = do
  (ty',_) <- lookupBinding n
  unless (ty `aeq` ty') $ do
         dty <- disp ty
         dty' <- disp ty'
         err $ "Var inferred typed '" ++ render dty' ++
             "' doesn't match expected type '" ++ render dty++"'"

  return ty
proofAnalysis (Con n) ty = do
  (ty',_) <- lookupBinding n
  unless (ty `aeq` ty') $ do
         dty <- disp ty
         dty' <- disp ty'
         err $ "Constructor inferred typed " ++ render dty' ++
             " doesn't match expected type " ++ render dty

  return ty


proofAnalysis (Contra p) ty = do
 ty' <- proofSynth p
 case down ty' of
   (Equal t1 t2) ->
     -- TODO: Check that t1, t2 are typeable, and that all arguments are values.
     case (findCon (down t1),findCon (down t2)) of
       (Just c1, Just c2) -> do
          unless (c1 /= c2) $ err "In contra, constructors must be unique."
          return ty
       _ -> do
         err "In contra, equality proof must be between constructor values."


  where findCon (Con c) = Just c
        findCon (Pos _ t) = findCon t
        findCon (Parens t) = findCon t
        findCon (App t1 _ _) = findCon t1
        findCon _ = Nothing


proofAnalysis (ContraAbort taborts tterminates) ty = do
  aborts <- proofSynth taborts
  terminates <- proofSynth tterminates
  case (down aborts,down terminates) of
    (Equal (Abort _) s, Terminates s') -> do
       unless (down s `aeq` down s') $ do
          ds <- disp s
          ds' <- disp s'
          err $ "Can't use contrabort'" ++ render ds ++ "' doesn't match '" ++
              render ds' ++"'"  -- ++ \n   "++show (down s)++"\n   "++show (down s')
       return ty
    _ -> do
      da <- disp aborts
      dt <- disp terminates
      err $ "Can't use contrabort: " ++ render da ++ " and  " ++
              render dt ++ " are the wrong form."


proofAnalysis (t@(Val x)) ty =
  do let f t = do ty <- typeSynth t
                  case down ty of
                   (Terminates x) -> return x
                   _ -> throwError $ strMsg $ "Can't escape to something not a Termination in valCopy"
     term <- escCopy f x
     typeSynth term
     stub <- escCopy (\ x -> return Type) x
     b <- synValue stub
     if b
        then do let ans = Terminates (down term)
                unless (ans `aeq` down ty) $ do
                   xd <- disp x
                   ansd <- disp ans
                   tyd <- disp ty
                   err $ "In (value " ++ render xd ++ ") the type\n   " ++render ansd++
                         "\ndoesn't match the expexted type\n   "++ render tyd
                return ans
        else  do d <- disp t
                 err $ "Non Value: " ++ render d


proofAnalysis proof pred = do
  d <- disp (Ann proof pred)
  err $ "Unmatched proofAnalysis: " ++ render d



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
      -- liftIO  $ putStrLn $ "ty is " ++ render dty ++ "\n ++ t is " ++ render dt
      case down ty of
        Equal (Abort _) e -> -- return e
                              typeSynth e
        _ -> do
          dty <- disp ty
          throwError $
               strMsg $ "In strict context, witness of abort" ++
                      render dty ++ " equality is ill-formed."

typeSynth (ConvCtx t ctx) = do
  l <- copyEqualInEsc LeftContext ctx
  lty <- withEscapeContext LeftContext $ typeSynth l
  proofAnalysis t l
  r <- copyEqualInEsc RightContext ctx
  rty <- withEscapeContext RightContext $ typeSynth r
  return r


typeSynth (Ann t ty) = do
  typeAnalysis t ty
  return ty

typeSynth (Abort t) = do
  typeAnalysis t Type
  return t

typeSynth (Terminates t) = do
  typeSynth t
  return $ Formula 0

typeSynth (Pi _ binding)  = do -- Term_Pi
  ((n,Embed ty),body) <- unbind binding
  extendBinding n ty False $ typeSynth body
  return Type


typeSynth (Equal t0 t1) = do
  k0 <- typeSynth t0
  typeAnalysis k0 Type
  k1 <- typeSynth t1
  typeAnalysis k1 Type
  return Type


typeSynth (Sym t) = do
  ty <- proofSynth  t
  case down ty of
     (Equal t1 t0)-> return (Equal t0 t1)
     _  ->
       err "Sym's argument must have the type of an equality proof."


typeSynth (Let binding) = do
    ((n,pf,Embed t),body) <- unbind binding
    ty' <- typeSynth t
    -- what is the value annotation for this?
    extendBinding n ty' True $
     extendBinding pf (Equal (Var n) t) True $
      typeSynth body


typeSynth t =  do
  dt <- disp t
  err $ "TODO: typeSynth: " ++ render dt


typeAnalysis (Parens t) ty = typeAnalysis t ty
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
  ensure (ty' `aeq` ty) $
        "Constructor " <++> t <++> "has type" <++> ty' <++> ", which doesn't match expected type" <++> ty

  return ty


typeAnalysis (Rec progBinding) res@(Pi Dynamic piBinding) = do -- Term_Rec
  -- FIXME: This is a hack, because there are different number of binders in the
  -- Rec and Pi forms, which doesn't seem to play well with unbind2.
  (p1@(f,_),body) <- unbind progBinding
  (p2,piBody) <- unbind piBinding
  Just ((f,(arg,Embed ty)),body,(_,(piArg,Embed piTy)),piBody)
    <- unbind2 (bind p1 body) (bind (f,p2) piBody)

  ensure (ty `aeq` piTy) $
         "Type " <++> ty <++> " ascribed to lambda bound variable " <++>
         "does not match type " <++> piTy <++> "ascribed to pi-bound variable."

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

typeAnalysis (Case _ _ _) ty = return ty
typeAnalysis (Case s Nothing binding) ty = do
    (sEq,alts) <- unbind binding
    typeSynth s
    mapM (altAnalysis sEq) alts
    return ty
  where altAnalysis eqpf alt = do
          -- FIXME: We need to make sure that constructors belong to the type of
          -- the scruinee, and that all cases are covered.
          ((cons,vars),body) <- unbind alt
          (ctype,_) <- lookupBinding (string2Name cons)
          dctype <- disp ctype
          let pat = foldl (\t0 t1 -> (App t0 Dynamic t1))
                      (Con (string2Name cons)) (map Var vars)

          ty' <- substPat vars ctype $
                   extendBinding eqpf (Equal pat s) True  $ typeAnalysis body ty
          return ty'


        substPat [] ty m = m
        substPat (n:ns) ty m =
          case down ty of
            (Pi _ binding) -> do
             ((n',Embed ty),body) <- unbind binding
             extendBinding n ty True $ substPat ns body m






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
             sub `expectType` ty
             return ty


    _ -> err $ "Can't apply a term " ++ show t0 ++
               " with type " ++ show ty0


typeAnalysis tm@(Var x) ty = do
  ty' <- typeSynth tm
  ty `expectType` ty'
  return ty


typeAnalysis (Escape t) ty = do
  ty <- typeSynth t
  dty <- disp ty
  dt <- disp t
  -- liftIO  $ putStrLn $ "ty is " ++ render dty ++ "\n ++ t is " ++ render dt
  escctx <- asks escapeContext
  case escctx of
    NoContext -> err "Can't have an escape outside of a context."
    LeftContext -> err "typeAnalysis: Escape in LeftContext not implemented."
    RightContext -> err "typeAnalysis: Escape in RightContext not implemented."
    StrictContext -> do
      ty <- typeSynth t
      case down ty of
        Equal (Abort _) e -> return e -- typeAnalysis e ty
        _ -> do
          die $ "In strict context, witness of abort" <++>
                 ty <++> "equality is ill-formed."




typeAnalysis (ConvCtx t ctx) ty = do
  l <- copyEqualInEsc LeftContext ctx
  lty <- withEscapeContext LeftContext $ typeSynth l
  proofAnalysis t l
  r <- copyEqualInEsc RightContext ctx
  rty <- withEscapeContext RightContext $ typeSynth r
  ensure (ty `aeq` r) $
     "RHS of conv" <++> r <++> "does not match expected type" <++> ty
  return r




typeAnalysis t ty = do
  d <- disp (Ann t ty)
  err $ "TODO: typeAnalysis" ++ render d


-- FIXME: This needs to try to synthesize (analyze) a type for everything in the b
-- syntactic class, not just terms.
bSynth t = do
  cls <- getClassification t
  case cls of
   SortType -> typeSynth t
   SortPred -> proofSynth t

bAnalysis t ty = do
  cls <- getClassification ty
  case cls of
   SortType -> typeAnalysis t ty
   SortPred -> proofAnalysis t ty



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
isProof (Case scrutinee (Just termWitness) binding) =
  isTerm scrutinee && ok
 where chkAlt a = let ((c,as),alt) = unsafeUnbind a in isProof alt
       ok = case unsafeUnbind binding of
              (cpf,alts) -> and (map chkAlt alts)
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
  ensure (p t) $ t <++> "is not the proper syntactic class (" <++> cls <++> ")."



-- Placeholder for op. semantics
join lSteps rSteps t1 t2 = do
  t1' <-  substDefs t1 >>= eval
  t2' <- substDefs t2 >>= eval
  ensure (t1' `aeq` t2') $
         t1' <++> " and " <++> t2' <++> "are not joinable."


  return (Equal t1 t2)
  -- unless (t1 `aeq` t2) $ err "Terms not joinable"




-- Get the classification of a classifier (Type,Predicate,LogicalKind)
data Sort = SortType | SortPred | SortLK deriving (Eq,Show)
getClassification (Pos _ t) = getClassification t
getClassification (Parens t) = getClassification t
getClassification t = do
  ta `comb` pa `comb` la `comb` end
  where ta = typeAnalysis t Type >> return SortType
        pa = do sort <- predSynth t
                unless (isLK (down sort)) $ err "Not a predicate"
                return SortPred
        la = do unless (isLK t) (err "Could not classify classifier")
                return SortLK
        comb a b = a `catchError` (\_ -> b)
        end = do env <- asks gamma
                 -- liftIO  $ mapM print env
                 die $ "Can't classify " <++> t

-----------------------------------------------
-- Generic function for copying a term and
-- handling the escape clause in a specific manner



-- escCopy f (Var x) = return(Var x)
-- escCopy f (Con x) = return(Con x)
-- escCopy f (Formula n) = return(Formula n)
-- escCopy f Type = return Type
-- escCopy f (Pi stage binding) = do
--   ((n,Embed ty),body) <- unbind binding
--   ty' <- escCopy f ty
--   body' <- escCopy f body
--   return $ Pi stage (bind (n,Embed ty') body')
-- escCopy f (Forall binding) = do
--   ((n,Embed ty),body) <- unbind binding
--   ty' <- escCopy f ty
--   body' <- escCopy f body
--   return $ Forall (bind (n,Embed ty') body')
-- escCopy f (App x s y) = lift2 app (escCopy f x) (escCopy f y)
--   where app x y = App x s y
-- escCopy f (Ann x y) = lift2 Ann (escCopy f x) (escCopy f y)
-- escCopy f (Equal x y) = lift2 Equal (escCopy f x) (escCopy f y)
-- escCopy f (Terminates x) = lift1 Terminates (escCopy f x)
-- escCopy f (Val x) = lift1 Val (escCopy f x)
-- escCopy f (Abort x) = lift1 Abort (escCopy f x)
-- escCopy f (Contra x) = lift1 Contra (escCopy f x)
-- escCopy f (ConvCtx x y) = lift2 ConvCtx (escCopy f x) (escCopy f y)
-- escCopy f (Parens x) = escCopy f x
-- escCopy f (Pos x t) = lift2 Pos (return x) (escCopy f t)
-- escCopy f (Escape t) = f t
-- escCopy f t =
--   do td <- disp t
--      error ("Not implemented yet in escCopy: "++render td)

escCopy :: (Term -> TCMonad Term) -> Term -> TCMonad Term
escCopy f t = everywhereM (mkM f') t
  where f' (Escape t) = f t
        f' t = return t

copyEqualInEsc b x = escCopy f x
 where f t  = do ty <- typeSynth t
                 case down ty of
                  (Equal l r) ->
                     case b of
                       LeftContext -> return l
                       RightContext -> return r
                       _ -> throwError $ strMsg $ "Copy can't reach this."
                  _ -> throwError $ strMsg $ "Can't escape to something not an equality"




