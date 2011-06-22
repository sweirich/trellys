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
import Data.List(nubBy, nub, (\\))



typecheck :: Module -> IO (Either TypeError ())
typecheck mod = do
  runErrorT $ runFreshMT $ runReaderT (runTCMonad (typecheckModule mod)) emptyEnv



-- * Running the typechecker.

-- | Typecheck an entire module
typecheckModule (Module n decls) = do
  checkDefs decls
  -- liftIO  $ putStrLn "Typecheck passed"
  return ()


data DefRes = DataResult TName Term [(TName,Int,Term)]
            | ProofResult TName Term Term Bool
            | ProgResult TName Term Term Bool

-- | Typecheck a single definition
checkDef (ProofDecl nm theorem proof) = do
  lk <- predSynth' theorem
  isLK <- lkJudgment lk
  ensure isLK ("Theorem is not a well-formed logical kind " <++> nm)

  proofAnalysis' proof theorem
  return $ ProofResult nm theorem proof False

checkDef (ProgDecl nm ty prog) = do
  typeAnalysis' ty Type
  typeAnalysis' prog ty
  return $ ProgResult nm ty prog False

checkDef (DataDecl (Con nm) ty cs) = do
  ran <- arrowRange ty
  ty `expectType` Type

  -- Make sure that the type constructor is a well-formed type.
  typeAnalysis' ty Type

  conTypes <- extendBinding nm ty True $
              mapM chkConstructor cs


  return (DataResult nm Type conTypes)


  where arrowRange (Pi _ binding) = do
          ((n,_),body) <- unbind binding
          arrowRange body
        arrowRange (Pos _ t) = arrowRange t
        arrowRange ty = return ty

        appHead (App t0 _ _) = appHead t0
        appHead (Pos _ t) = appHead t
        appHead t = t

        arity (Pi _ binding) = 1 + arity body
          where (_,body) = unsafeUnbind binding
        arity (Pos _ t) = arity t
        arity t = 0


        chkConstructor (c,ty) = do
           typeAnalysis' ty Type
           ran <- arrowRange ty
           case appHead ran of
             Con tc -> do
               ensure (tc == nm) $
                        "In constructor " <++> c <++>
                        "result type does not match declared data type."
               return (c,arity ty,ty)
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
          extendTypeCons n [(c,arity) | (c,arity,_) <- cs] $
          extendBinding n ty True $
                        foldr (\(n,arity,ty) m -> extendBinding n ty True m) comp cs




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



data CheckMode = PredMode | ProofMode | ProgMode deriving (Show,Eq)


check :: CheckMode -> Term -> Maybe Term -> TCMonad Term
check mode (Pos p t) expect  = check mode t expect `catchError` addErrorPos p t
check mode t (Just (Pos _ expect)) = check mode t (Just expect)

check mode (Ann t ty) Nothing = check mode t (Just ty)
check mode (Ann t ty) (Just ty') = do
  unless (ty `aeq` ty') $ do
    die $ "Annotated type" <++> ty' <++> "doesn't match" <++> ty
  check mode t (Just ty)


-- Var
check mode (Var n) expected = do
  (ty,_) <- lookupBinding n
  ty `sameType` expected

  case mode of
    ProgMode -> return ()
    ProofMode -> do
      requireA ty
      pty <- predSynth' ty
      requireQ pty
    PredMode -> err "Can't check variables in pred mode"
  return ty


-- Con
check mode (Con t) expected = do
  (ty,_) <- lookupBinding t
  ty `sameType` expected

  case mode of
    PredMode -> err "Can't check constructors in pred mode"
    _ -> return ()

  return ty


-- Formula

-- Type

check ProgMode Type Nothing = return Type
check ProgMode Type (Just Type) = return Type -- Term_Type
check _ Type _ = err "Can't check Type in non-programmatic mode."

-- Pi

check ProgMode (Pi _ binding) expected = do -- Term_Pi
  ((n,Embed ty),body) <- unbind binding
  extendBinding n ty False $ check ProgMode body expected

check mode (Pi _ _) _ = do
  err "Can't check Pi type in non-programmatic mode."


-- Forall
check PredMode (Forall binding) Nothing = do
  ((n,Embed t),body) <- unbind binding
  -- We need to do a syntactic case-split on ty. Going to use backtracking for now.
  case down t of
    Formula i -> do  -- Pred_Forall3 rule
           form <- extendBinding n t False (predSynth' body)
           (Formula j) <- guardFormula form
           return (Formula (max (i+1) j))
    (Forall binding') -> do -- Pred_Forall4 rule
           guardLK t
           form <- extendBinding n t False (predSynth' body)
           guardFormula form

    dom -> do
      cls <- getClassification dom
      case cls of
        SortPred -> do  -- Pred_Forall1
          lk <- predSynth' dom
          case lk of
            Formula i -> do
                    extendBinding n dom False (predSynth' body)
            _ -> do
                err "predSynth pred case, not a formula."
        SortType -> do
                 ty <- typeSynth' t
                 dty <- disp ty
                 -- unless (ty `aeq` Type) $
                 --      err $ "Expecting a type for " ++ render dty
                 ty `expectType` Type


                 form <- extendBinding n t False (predSynth' body)
                 guardFormula form
  where guardFormula t@(Formula i) = return t
        guardFormula _ = err "Not a formula"

check mode (Forall _) _ = do
  err "Can't check Forall tpe in non-predicate mode."

-- App


check mode term@(App t0 stage t1) expected = do
  ty0 <- check mode t0 Nothing
  case (mode, down ty0) of
    (ProgMode, Pi piStage binding) -> do
        ensure (piStage == stage) $ do
                 "Stage" <++> show piStage <++>  "for arrow" <++>
                  "does not match stage for application " <++> show stage

        ((x,Embed dom),body) <- unbind binding
        argTy <- typeAnalysis' t1 dom   -- TODO: Check on this, should it be typeAnalysis?
        requireA argTy
        require_a t1
        let sub = subst x t1 body
        sub `sameType` expected
        return sub

    (PredMode, Forall binding) -> do
        ensure (stage == Static) $
               err "Application of a predicate must be in the static stage."
        ((n,Embed ty),body) <- unbind binding
        guardLK body
        typeAnalysis' t1 ty -- TODO: Check on this, should it be typeAnalysis?
        return $ subst n t1 body
    (ProofMode, Forall binding) -> do
        ((n,Embed ty),body) <- unbind binding
        requireB ty
        requirePred body
        bty <- bAnalysis t1 ty
        let snb = subst n t1 body
        snb `sameType` expected
        return snb
    (ProofMode, Pi stage binding) -> do
             -- FIXME: Do something with the stage?
             ((n,Embed ty),body) <- unbind binding
             -- requireB ty
             -- requirePred body
             bty <- bAnalysis t1 ty
             let snb = subst n t1 body
             ensure (constrApp term) $ term <++> "is not a construction."
             snb `sameType` expected
             return snb
    _ -> checkUnhandled mode term expected
  where constrApp (Con c) =  True
        constrApp (App f _ x) = (constrApp f)
        constrApp (Pos x t) = constrApp t
        constrApp _ = False


-- Lambda

-- TODO: For now, we leave these as separate clauses. Perhaps we should revisit
-- and refactor these at some point.
check PredMode (Lambda Form Static binding) Nothing = do -- Pred_Lam rule
  ((n,Embed ty),body) <- unbind binding
  -- First Premise
  ensure (isW ty) $ ty <++> "is not in the 'W' syntactic class."
  -- Second Premise
  form <- extendBinding n ty False (predSynth' body)
  lk <- lkJudgment form
  ensure lk $ form <++> " is not a valid logical kind."
  return (Forall (bind (n,Embed ty) form))

check ProofMode (Lambda Form _ pfBinding)
              (Just out@(Forall predBinding)) = do -- Prf_Forall.

  Just ((proofName,Embed pfTy),pfBody,(predName,Embed predTy),predBody) <-
    unbind2  pfBinding predBinding
  pfKind <- typeSynth' pfTy
  requireQ pfKind

  -- Whether the var should be marked value or not is sort of up in the air...
  extendBinding proofName pfTy False (proofAnalysis' pfBody predBody)
  return out


check ProgMode (Lambda Program progStage progBinding) (Just ty@(Pi piStage piBinding)) = do
  unless (progStage == piStage) $
         err $ "Lambda stage annotation " ++ show progStage ++ " does not " ++
               "match arrow annotation " ++ show piStage

  ((progName,Embed progTy), progBody) <- unbind progBinding
  ((piName,Embed piTy), piBody) <- unbind piBinding

  -- TODO: Several side conditions on stage annotations
  extendBinding progName progTy True $ typeAnalysis' progBody piBody



-- Case
check mode (Case s pf binding) expected = do
  ensure (mode `elem` [ProofMode,ProgMode]) $
         die $ "Case expressions can only be checked in proof and program mode, not " <++> show mode
  (sEq,alts) <- unbind binding
  tyS <- typeSynth' s

  -- Checking termination proof
  case (mode,pf) of
      (ProofMode,Just termProof) -> do
                     sTermType <- proofSynth' termProof
                     ensure (sTermType `aeq` Terminates s) $
                       termProof <++> "is not a proof of" <++> (Terminates s)
      (ProofMode, Nothing) -> do
                     err "When case-splitting in a proof, a termination proof must be supplied."
      _ -> return ()

  checkCaseCoverage tyS alts
  tys <- mapM (altAnalysis sEq) alts
  case nubBy aeq tys of
    [] -> maybe (err "Can't infer a type for a case expression with no branches.") return expected
    [l] -> do
      l `sameType` expected
      return l

    ls -> err "Types of case alternatives do not match"


  where altAnalysis eqpf alt = do
          ((cons,vars),body) <- unbind alt
          (ctype,_) <- lookupBinding (string2Name cons)


          let pat = foldl (\t0 t1 -> (App t0 Dynamic t1))
                      (Con (string2Name cons)) (map Var vars)

          substPat vars ctype $
            extendBinding eqpf (Equal pat s) True  $ check mode body expected


        substPat [] ty m = m
        substPat (n:ns) ty m =
          case down ty of
            (Pi _ binding) -> do
             ((n',Embed ty),body) <- unbind binding
             extendBinding n ty True $ substPat ns body m




-- TerminationCase
check ProofMode (TerminationCase s binding) (Just ty) = do
  sty <- typeSynth' s
  (w,(abort,terminates)) <- unbind binding
  extendBinding w (Equal (Abort sty) s) True (proofAnalysis' abort ty)
  extendBinding w (Terminates s) True (proofAnalysis' terminates ty)
  return ty

-- Join
check ProofMode (Join lSteps rSteps) (Just eq@(Equal t0 t1)) = do
  typeSynth' t0
  typeSynth' t1
  -- FIXME: Need to define operational semantics.
  join lSteps rSteps t0 t1
  return eq

-- Equal
check mode term@(Equal t0 t1) expected = do
  ty0 <- typeSynth' t0
  ty1 <- typeSynth' t1
  typeAnalysis' ty0 Type
  typeAnalysis' ty1 Type
  case (mode,expected) of
    (PredMode, Nothing) -> do
       return (Formula 0)
    (ProofMode, Nothing) -> do
       return Type -- FIXME: What rule does this correspond to?
    (ProgMode, Nothing) -> do
       return Type -- FIXME: What rule does this correspond to?
    _ -> checkUnhandled mode term expected

-- Val

check ProofMode (t@(Val x)) expected = do
     let f t = do ty <- typeSynth' t
                  case down ty of
                   (Terminates x) -> return x
                   _ -> err $ "Can't escape to something not a Termination in valCopy."
     term <- escCopy f x
     typeSynth' term
     stub <- escCopy (\ x -> return Type) x
     b <- synValue stub
     if b
        then do let ans = Terminates (down term)
                ans `sameType` expected
                return ans
        else  do d <- disp t
                 err $ "Non Value: " ++ render d



-- Terminates

check mode (Terminates t) expected = do -- Pred_Terminates rule
  ensure (mode `elem` [PredMode,ProgMode]) $
         die $ "Can't check type of Terminates term in " <++> show mode <++> "mode."
  typeSynth' t
  (Formula 0) `sameType` expected
  return (Formula 0)


-- Contra

check ProofMode (Contra p) (Just ty) = do
 ty' <- proofSynth' p
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
        findCon (App t1 _ _) = findCon t1
        findCon _ = Nothing

-- ContraAbort

check ProofMode (ContraAbort taborts tterminates) (Just ty) = do
  aborts <- proofSynth' taborts
  terminates <- proofSynth' tterminates
  case (down aborts,down terminates) of
    (Equal (Abort _) s, Terminates s') -> do
       ensure (down s `aeq` down s') $
                "Can't use contrabort'" <++> s <++> "' doesn't match '" <++>
                s' <++> "'"
       return ty



    _ -> die $ "Can't use contrabort: " <++> aborts <++> "and" <++>
              terminates <++> "are the wrong form."

-- Abort
-- TODO: Is this even used?
check ProgMode (Abort t) Nothing = do
  typeAnalysis' t Type
  return t


-- Conv

-- ConvCtx
check mode (ConvCtx p ctx) expected = do
  ensure (mode `elem` [ProofMode,ProgMode]) $
         die $  "Can't do conversion in mode" <++> show mode
  let submode = case mode of
                  ProofMode -> PredMode
                  ProgMode -> ProgMode
                  _ -> error "Unreachable case in check of ConvCtx def."
  l <- copyEqualInEsc LeftContext ctx
  lty <- withEscapeContext LeftContext $ check submode l Nothing
  proofAnalysis' p l
  r <- copyEqualInEsc RightContext ctx
  rty <- withEscapeContext RightContext $ check submode r Nothing
  r `sameType` expected
  return r


-- Ord

check ProofMode (Ord w) (Just ty@(IndLT l r)) = do
  -- Skeleton version of the 'ord' axiom.
  ty' <- proofSynth' w
  case down ty' of
    (Equal l' r') -> do
        let (c,ls) = splitApp' l'
        ensure (r `aeq` r' && any (aeq l) ls)
                 $ "Ord error" <++> ty' $$$
                   r <++> "/=" <++> r' <++> "or" $$$
                   l <++> "not in" <++> show ls

        return ty

-- IndLT

check PredMode (IndLT t0 t1) Nothing = do
  ty0 <- typeSynth' t0
  ty1 <- typeSynth' t1
  -- TODO: Do we need to check to see that ty0 and t1 : Type?
  return (Formula 0)


-- OrdTrans

check ProofMode t@(OrdTrans p1 p2) (Just ty@(IndLT y x)) = do
  ty1 <- proofSynth' p1
  ty2 <- proofSynth' p2
  case (down ty1,down ty2) of
    (IndLT y' z, IndLT z' x')
      | z `aeq` z' && y `aeq` y' && x `aeq` x' ->
          return ty
      | otherwise -> die $ "Bad ordtrans" <++> t <++> ty1 <++> ty2 <++> ty
    _ -> die $ "Bad ordtrans" <++> t <++> ty1 <++> ty2 <++> ty

-- Ind

-- res should have the form (\forall x:t1 . \forall u:x! . P)
check ProofMode (Ind prfBinding) (Just res@(Forall predBinding)) = do -- Prf_Ind
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
    extendBinding f fty True $ proofAnalysis' proofBody predBody

  return res


-- Rec

check ProgMode (Rec progBinding) (Just res@(Pi Dynamic piBinding)) = do -- Term_Rec
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
    extendBinding arg ty True $ typeAnalysis' body piBody
  return res

-- Escape


check ProgMode (Escape t) expected = do
  escctx <- asks escapeContext
  case escctx of
    NoContext -> throwError $ strMsg "Can't have an escape outside of a context."
    LeftContext -> do
       ty <- typeSynth' t
       case down ty of
         (Equal l _) -> return l
         _ -> throwError $ strMsg "Can't cast by something not an equality proof."

    RightContext -> do
       ty <- typeSynth' t
       case down ty of
         (Equal _ r) -> return r
         _ -> throwError $ strMsg "Can't cast by something not an equality proof."
    StrictContext -> do
      ty <- typeSynth' t
      case down ty of
        Equal (Abort _) e -> typeSynth' e
        _ -> die $ "In strict context, witness of abort" <++>
                      ty <++> "equality is ill-formed."



-- Let

check mode (Let binding) expected = do
    unless (mode `elem` [ProofMode,ProgMode]) $
           die $ "Let expressions cannot be checked in" <++> show mode <++> "mode."
    ((n,pf,Embed t),body) <- unbind binding
    ty' <- check mode t Nothing
    -- what is the value annotation for this?
    extendBinding n ty' True $
     extendBinding pf (Equal (Var n) t) True $
      check mode body expected


-- Aborts

check ProofMode (Aborts c) expected = withEscapeContext StrictContext $ do
  cty <- typeSynth' c
  case isStrictContext c of
    Nothing -> throwError $ strMsg "Not a strict context"
    Just (e,f) -> do
      eqTy <- typeSynth' e
      case down eqTy of
        (Equal (Abort t) e2) -> do
           let ty' = Equal (Abort t) (f e2)
           ty' `sameType` expected
           return ty'
        _ -> throwError $ strMsg
               "In strict, the context hole is not of the proper form abort = e"


-- Sym
check mode (Sym t) expected = do
  ensure (mode `elem` [ProgMode, ProofMode]) $
         die $ "Can't check sym in mode" <++> show mode
  ty <- check ProofMode t Nothing
  case down ty of
     (Equal t1 t0)-> return (Equal t0 t1)
     _  ->
       err "Sym's argument must have the type of an equality proof."


check ProgMode (Sym t) Nothing  = do
  ty <- proofSynth'  t
  case down ty of
     (Equal t1 t0)-> return (Equal t0 t1)
     _  ->
       err "Sym's argument must have the type of an equality proof."

check ProofMode (Sym t) Nothing = do
  ty <- proofSynth'  t
  case down ty of
     (Equal t1 t0)-> return (Equal t0 t1)
     _  ->
       err "Sym's argument must have the type of an equality proof."

check ProofMode (Sym t) (Just ty@(Equal t0 t1)) = do
  proofAnalysis' t (Equal t1 t0)
  return ty

check mode term expected = checkUnhandled mode term expected

checkUnhandled mode term expected = do
  die $  "Unhandled check case:" $$$
          "mode: " <++> show mode $$$
          "term: " <++> term $$$
          "expected: " <++> expected


predSynth' t = check PredMode t Nothing
proofSynth' t = check ProofMode t Nothing
proofAnalysis' t ty = check ProofMode t (Just ty)
typeSynth' t = check ProgMode t Nothing
typeAnalysis' t ty = check ProgMode t (Just ty)





-- FIXME: This needs to try to synthesize (analyze) a type for everything in the b
-- syntactic class, not just terms.
bSynth t = do
  cls <- getClassification t
  case cls of
   SortType -> typeSynth' t
   SortPred -> proofSynth' t

bAnalysis t ty = do
  cls <- getClassification ty
  case cls of
   SortType -> typeAnalysis' t ty
   SortPred -> proofAnalysis' t ty



-- Syntactic class predicates (TODO)
isA t = isTerm t || isPred t
isB t = isTerm t || isPred t || isLK t

-- isB t = do
--   c <- getClassification t
--   return $ c `elem` [SortType

isW Type = True
isW (Formula _) = True
isW (Pos _ t) = isW t

isW _ = False

isQ Type = True
isQ (Formula _) = True
isQ (Pos _ t) = isQ t
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
getClassification t = do
  ta `comb` pa `comb` la `comb` end
  where ta = typeAnalysis' t Type >> return SortType
        pa = do sort <- predSynth' t
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
 where f t  = do ty <- typeSynth' t
                 case down ty of
                  (Equal l r) ->
                     case b of
                       LeftContext -> return l
                       RightContext -> return r
                       _ -> throwError $ strMsg $ "Copy can't reach this."
                  _ -> throwError $ strMsg $ "Can't escape to something not an equality"



checkCaseCoverage tyS alts = do
    -- Checking constructor coverage
    let (tc,_) = splitApp' tyS
    cs <- case down tc of  -- declared (constructor, arity)
           (Con tcName) -> lookupTypeCons tcName
           _ -> die $ "Can't find type constructor" <++> show tc


    altCs <- forM alts (\a -> do { ((n,vars),_) <- unbind a; return (string2Name n, length vars)})

    let unhandled =  (nub $ map fst cs) \\ (nub $ map fst altCs)
    ensure (null unhandled) $
           "Unhandled constructors:" <++> (vcat <$> mapM disp unhandled :: TCMonad Doc)

    forM altCs (\(n,arity) -> case lookup n cs of
                                Nothing -> die $ n <++> "is not a constructor of" <++> tc
                                Just arity'
                                     | arity == arity' -> return ()
                                     | otherwise -> die $ "Pattern arity" <++> arity <++>
                                                          "does not match constructor" <++> n <++>
                                                          "arity" <++> arity')
