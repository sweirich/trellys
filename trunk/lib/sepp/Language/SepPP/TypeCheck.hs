{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

module Language.SepPP.TypeCheck where

import Language.SepPP.Syntax
import Language.SepPP.PrettyPrint
import Language.SepPP.Eval
import Language.SepPP.TCUtils
import Language.SepPP.Options
import Language.SepPP.Match

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
import Data.List(nubBy, nub, (\\),intersect,sortBy,groupBy)
import qualified Data.Map as M


typecheck :: Module -> IO (Either TypeError ())
typecheck mod = do
  runErrorT $ runFreshMT $ runReaderT (evalStateT (runTCMonad (typecheckModule mod)) flagMap) emptyEnv

-- * Running the typechecker.

-- | Typecheck an entire module
typecheckModule (Module n decls) = do
  checkDefs decls
  -- liftIO  $ putStrLn "Typecheck passed"
  return ()


data DefRes = DataResult EName Tele [(EName,(Int,Expr))]
            | ProofResult EName Expr Expr Bool
            | ProgResult EName Expr Expr Bool
            | AxiomResult EName Expr
            | FlagResult String Bool
            | OperatorResult String

-- | Typecheck a single definition
checkDef :: Decl -> TCMonad DefRes
checkDef (FlagDecl nm b) = return $ FlagResult nm b
checkDef (OperatorDecl nm level fixity) = return $ OperatorResult nm

checkDef (AxiomDecl nm theorem) = do
  lk <- predSynth' theorem
  isLK <- lkJudgment lk
  ensure isLK ("Theorem is not a well-formed logical kind " <++> nm)
  return $ AxiomResult nm theorem

checkDef (ProofDecl nm theorem proof) = do
  lk <- predSynth' theorem
  isLK <- lkJudgment lk
  ensure isLK ("Theorem is not a well-formed logical kind " <++> nm)

  proofAnalysis' proof theorem
  return $ ProofResult nm theorem proof False

checkDef (ProgDecl nm ty prog) = do
  typeAnalysis' ty Type
  typeAnalysis' prog ty
  isVal <- synValue prog
  return $ ProgResult nm ty prog isVal

checkDef (DataDecl (Con nm) binding) = do
  (tele,cs) <- unbind binding

  -- Turn the telescope (from the type arguments to the type
  -- constructor) into a dependent product.
  let ty = teleArrow tele Type
  ran <- arrowRange ty

  withErrorInfo "When checking the range of a type constructor"
                  [(text "The Type Constructor", disp nm)] $ ran `expectType` Type

  -- Make sure that the type constructor is a well-formed type.
  withErrorInfo "When checking that a type constructor is kindable."
                [(text "The Type Constructor", disp nm)
                ,(text "The Type",disp ty)] $ typeAnalysis' ty Type

  -- Change the erasure annotations of all type args to runtime using dynArrow.
  conTypes <- extendBinding nm (dynArrow ty) True $
               extendTele tele $ (mapM chkConstructor cs)
  return (DataResult nm tele conTypes)


  where arrowRange (Pi _ binding) = do
          ((n,_,_),body) <- unbind binding
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
               return (c,(arity ty,ty))
             h -> do
               die $ "Constructor head is" <++> h


checkDefs [] = return ()
checkDefs (d:ds) = do
  d <- checkDef d
  extendBinding' d (checkDefs ds)

  where extendBinding' (ProofResult n ty def v) comp =
          extendBinding n ty v comp
        extendBinding' (AxiomResult n ty) comp =
          extendBinding n ty False comp
        extendBinding' (ProgResult n ty def v) comp =
          extendDefinition  n ty def v comp
        extendBinding' (DataResult tnm tele cs) comp =
          extendTypeCons tnm tele cs $
          extendBinding tnm (dynArrow (teleArrow tele Type)) True $
                        foldr (\(cnm,(arity,ty)) m ->
                                 extendBinding cnm (teleArrow tele ty) True m)
                        comp cs
        extendBinding' (OperatorResult n) comp = comp
        extendBinding' (FlagResult n val) comp = do
           setFlag n val
           comp
        -- make all of the erasure annotations for the type
        -- constructor's type (kind) be runtime
        dynamicTele Empty = Empty
        dynamicTele (TCons binding) =
            TCons (rebind (n,Dynamic,ty,inf) (dynamicTele body))
          where ((n,_,ty,inf),body) = unrebind binding





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
  ((n,Embed ty,inf),body) <- unbind binding
  ensure (isA ty) $
    "Expecting the classifier for a logical kind argument to be syntax class"
    <++> "'A'."
  extendBinding n ty False (lkJudgment body)
lkJudgment (Pos _ t) = lkJudgment t
lkJudgment t = do
  typeError "Could not classify term as a logical kind"
            [(text "The Expr", disp $ show t)]

guardLK t = do
  lk <- lkJudgment t
  ensure lk (t <++> "is nota valid logical kind.")



data CheckMode = LKMode | PredMode | ProofMode | ProgMode deriving (Show,Eq)


check :: CheckMode -> Expr -> Maybe Expr -> TCMonad Expr
check mode (Pos p t) expect  = check mode t expect `catchError` addErrorPos p t
check mode t (Just (Pos _ expect)) = check mode t (Just expect)

check mode (Ann t ty) Nothing = check mode t (Just ty)
check mode (Ann t ty) (Just ty') = do
  ret <- check mode t (Just ty)
  unless (down ty `aeq` down ty') $
    typeError "The expected type does match the type given in an ascription."
      [(text "The expected type", disp ty'), (text "The ascribed type", disp ty)]
  return ret


-- Var
check mode tm@(Var n) expected = do


  (ty,_) <- lookupBinding n
  ty `sameType` expected
  return ty

  case mode of
    ProgMode -> return ()
    ProofMode -> do
      withErrorInfo "When checking that a variable is of the syntactic class 'A'."
                    [(text "The expression", disp tm)] $ requireA ty
      pty <- predSynth' ty
      requireQ pty
    PredMode -> typeError "Can't check variables in pred mode."
                  [(text "The expression",disp tm),
                   (text "The expected type", disp expected)]

  return ty


-- Con
check mode tm@(Con t) expected = do
  (ty,_) <- lookupBinding t
  ty `sameType` expected

  case mode of
    PredMode -> typeError "Can't check constructors in pred mode."
                  [(text "The expression",disp tm),
                   (text "The expected type", disp expected)]
    _ -> return ()
  return ty


-- Formula

-- Type

check ProgMode Type Nothing = return Type
check ProgMode Type (Just Type) = return Type -- Expr_Type
check _ Type _ = err "Can't check Type in non-programmatic mode."

-- Pi

check ProgMode tm@(Pi stage binding) expected = do -- Expr_Pi
  ((n,Embed ty,inf),body) <- unbind binding
  cls <- getClassification ty
  case cls of
    SortType -> return ()
    SortPred -> do
      unless (stage == Static) $
             typeError ("When checking a programmatic Pi-type, proof arguments" <++>
                       "must be marked erased.")
               [(text "The type", disp tm),
                (text "The argument", disp n)]
    _ -> typeError ("When checking programmatic Pi-type, the arguments" <++>
                    "must be classified as proofs or programs")
           [(text "The type", disp ty)
           ,(text "The argument", disp n)]





  extendBinding n ty False $ check ProgMode body expected

check mode tm@(Pi _ _) ty = do
  die $ "Can't check Pi type in non-programmatic mode." $$$
        tm $$$
        ty


-- Forall
check PredMode (Forall binding) Nothing = do
  ((n,Embed t,inf),body) <- unbind binding
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
                 ty `expectType` Type


                 form <- extendBinding n t False (predSynth' body)
                 guardFormula form
  where guardFormula t@(Formula i) = return t
        guardFormula _ = err "Not a formula"

check mode (Forall _) _ = do
  err "Can't check Forall tpe in non-predicate mode."

-- App

check mode term@(App t0 stage t1) expected = do
 imp <- getOptImplicitArgs
 if imp
   then do
       implicit mode term expected -- checkImp is defined way at the bottom.
   else do -- No implicit arguments
    ty0 <- check mode t0 Nothing
    case (mode, down ty0) of
     (ProgMode, Pi piStage binding) -> do
        ((x,Embed dom,inf),body) <- unbind binding
        cls <- getClassification dom
        argMode <- case cls of
                     SortPred -> return ProofMode
                     SortType -> return ProgMode
                     _ -> typeError ("The classifier of the argument to a programmatic application" <++>
                                    "should either be a predicate or program.")
                                    [(text "The application", disp term),
                                     (text "The classifier", disp dom)]

        argTy <- check argMode t1 (Just dom)
        withErrorInfo "The argument type does not have the syntactic classification A."
                        [(text "The argument", disp argTy)
                        ,(text "The application", disp term)
                        ] $  requireA argTy

        unless (piStage == stage) $ do
           typeError "The stage for the arrow does not match the stage for the application"
                        [(text "Arrow stage:",disp piStage),
                         (text "Application stage", disp stage)]


        -- withErrorInfo "require_a" [] $ require_a t1
        let sub = subst x t1 body
        sub `sameType` expected
        return sub
     (ProgMode, ty0') -> do
        typeError "Can't apply a expression that does not have an arrow type."
                  [(text "The Type", disp ty0')
                  ,(text "The Function", disp t0)
                  ,(text "The Application", disp term)]

     (PredMode, Forall binding) -> do
        ensure (stage == Static) $ "Application of a predicate must be in the static stage."
        ((n,Embed ty,inf),body) <- unbind binding
        guardLK body
        typeAnalysis' t1 ty -- TODO: Check on this, should it be typeAnalysis?
        return $ subst n t1 body
     (ProofMode, Forall binding) -> do
        ((n,Embed ty,inf),body) <- unbind binding
        requireB ty
        requirePred body
        bty <- bAnalysis t1 ty
        let snb = subst n t1 body
        snb `sameType` expected
        return snb
     (ProofMode, Pi stage binding) -> do
             -- FIXME: Do something with the stage?
             ((n,Embed ty,inf),body) <- unbind binding
             -- requireB ty
             -- requirePred body
             bty <- bAnalysis t1 ty
             let snb = subst n t1 body
             ensure (constrApp term) $ term <++> "is not a construction."
             snb `sameType` expected
             return snb
     (_, tyfun) -> typeError "App with non-function"
                  [(text "computed function type", disp tyfun)]
    -- _ -> checkUnhandled mode term expected
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
  return (Forall (bind (n,Embed ty,False) form))

check ProofMode (Lambda Form _ pfBinding)
              (Just out@(Forall predBinding)) = do -- Prf_Forall.

  Just ((proofName,Embed pfTy),pfBody,(predName,Embed predTy,predInf),predBody) <-
    unbind2  pfBinding predBinding

  cls <- getClassification pfTy
  -- emit $ disp pfTy <++> text (show cls)
  pfKind <- check (classToMode cls) pfTy Nothing
  requireQ pfKind

  -- Whether the var should be marked value or not is sort of up in the air...
  extendBinding proofName pfTy False (proofAnalysis' pfBody predBody)
  return out


check ProgMode (Lambda Program progStage progBinding) (Just ty@(Pi piStage piBinding)) = do
  unless (progStage == piStage) $
         typeError "When checking a lambda-term against a pi-type, the stage annotations do not match."
                   [(text "The Lambda stage annotation", disp $ show progStage)
                   ,(text "The Pi stage annotation", disp $ show piStage)
                   ]

  Just ((progName,Embed progTy), progBody,(piName,Embed piTy,piInf), piBody) <-
    unbind2 progBinding piBinding

  -- TODO: Several side conditions on stage annotations
  extendBinding progName progTy True $ typeAnalysis' progBody piBody


check ProgMode (Lambda Program stage binding) Nothing = do
  ((nm,Embed ty),body) <- unbind binding
  bodyTy <- extendBinding nm ty True $ check ProgMode body Nothing
  return $ Pi stage (bind (nm,Embed ty,False) bodyTy)




-- Case
check mode (Case s pf binding) expected = do
  ensure (mode `elem` [ProofMode,ProgMode]) $
     "Case expressions can only be checked in proof and program mode, not " <++> show mode
  (sEq,alts) <- unbind binding
  tyS <- typeSynth' s


  -- Checking termination proof
  case (mode,pf) of
      (ProofMode,Just termProof) -> do
                     sTermType <- proofSynth' termProof
                     ensure (down sTermType `aeq` Terminates s) $
                       termProof $$$
                        "with the type" <++> sTermType <++> "is not a proof of" $$$
                       (Terminates s)
      (ProofMode, Nothing) -> do
                     err "When case-splitting in a proof, a termination proof must be supplied."
      _ -> return ()

  -- Set up the parameter substitution

  (args,cs) <- checkCaseCoverage tyS alts
  tys <- mapM (altAnalysis args cs sEq) alts


  case nubBy aeq tys of
    [] -> maybe (err "Can't infer a type for a case expression with no branches.") return expected
    [l] -> do
      l `sameType` expected
      return l

    ls -> err "Types of case alternatives do not match"


  where altAnalysis args cs eqpf alt = do
          ((cons,vars),body) <- unbind alt
          ctype <-
            maybe (typeError "When checking a case alternative, can't find constructor"  [(text "The Constructor", disp cons)])
                  return (lookup (string2Name cons) cs)

          stages <- getStages ctype
          let pat = foldl (\t0 (t1,stage) -> (App t0 stage t1))
                      (Con (string2Name cons)) ([(a,Static) | a <- args] ++ [(Var v, st) | v <- vars | st <- stages])

          substPat vars ctype $
            extendBinding eqpf (Equal pat s) True  $ check mode body expected


        substPat [] ty m = m
        substPat (n:ns) ty m =
          case down ty of
            (Pi _ binding) -> do
             ((n',Embed ty,inf),body) <- unbind binding
             extendBinding n ty True $ substPat ns (subst n' (Var n) body) m
            _ -> typeError
                  ("When checking a pattern, expected constructor to have" <++>
                   "a pi-type.")
                  [(text "The Type", disp ty)]

        getStages (Pos _ t) = getStages t
        getStages (Pi st binding) = do
          ((n',_,_),body) <- unbind binding
          vs <- getStages body
          return $ st:vs
        getStages _ = return []



-- TerminationCase
check mode t@(TerminationCase s binding) expected = do
  unless (mode `elem` [ProofMode, ProgMode]) $
         typeError "Termination case is not valid in this mode."
                     [(text "The term", disp t)
                     ,(text "The mode", disp $ show mode)]
  sty <- typeSynth' s
  (w,(abort,terminates)) <- unbind binding
  ty1 <- extendBinding w (Equal (Abort sty) s) True  (check mode abort expected)
  ty2 <- extendBinding w (Terminates s) True (check mode terminates expected)
  unless (ty1 `aeq` ty2) $
    typeError "Termination case branch types do not match"
        [(text "The term", disp t)
        ,(text "Aborts branch type", disp ty1)
        ,(text "Terminates branch type", disp ty2)
        ]
  return ty1



-- Join
check ProofMode (Join lSteps rSteps) (Just eq@(Equal t0 t1)) = do
  typeSynth' t0
  typeSynth' t1
  join lSteps rSteps t0 t1
  return eq
check ProofMode tm@(Join _ _) (Just ty) = do
  typeError "join can only be used to prove an equality."
    [(text "The term", disp tm),
     (text "The desired type", disp ty)
     ]

-- MoreJoin

check mode t@(MoreJoin ps) (Just eq@(Equal t0 t1)) = do
  unless (mode `elem` [ProofMode,ProgMode]) $
     typeError "Morejoin is only valid in proof and programming mode."
               [(text "The Term", disp t)
               ,(text "The Mode", disp $ show mode)]
  (rs,ts) <- checkProofs ps
  withErrorInfo "When evaluating with rewrite rules, while checking a morejoin proof." []
    $ withTermProofs ts $ withRewrites rs (join 10000 10000 t0 t1)
  return eq

  where checkProofs [] = return ([],[])
        checkProofs (p:ps) = do
          ty <- withErrorInfo "When checking a proof supplied to morejoin." [ (text "The proof", disp p)] $
                  check ProofMode p Nothing
          case down ty of
            Equal t1 t2 -> do
                         et1 <- erase t1
                         et2 <- erase t2
                         (rs,ts) <- checkProofs ps
                         return ((et1,et2):rs,ts)

            Terminates t -> do
                (rs,ts) <- checkProofs ps
                t' <- erase t
                return (rs,t':ts)

            ty -> typeError
                    ("Term does not have the correct type to be used as a morejoin rewrite." <++>
                    "It must either be a equality or termination proof.")
                      [(text "The Expr", disp p),
                       (text "The Type", disp ty)]


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
        else do die $ "Non Value:" <++> t

check mode (TCast t p) expected = do
  ty <- check mode t expected
  check ProofMode p (Just (Terminates t))
  return ty

-- Terminates

check mode (Terminates t) expected = do -- Pred_Terminates rule
  ensure (mode `elem` [PredMode,ProgMode]) $
           "Can't check type of Terminates term in " <++> show mode <++> "mode."
  typeSynth' t
  (Formula 0) `sameType` expected
  return (Formula 0)


-- Contra

check mode tm@(Contra p) (Just ty) = do
 unless (mode `elem` [ProofMode, ProgMode]) $
   typeError "Can only check contradictions in proof or program mode."
     [(text "The mode", disp $ show mode)
     ,(text "The term", disp tm)
     ,(text "The type", disp ty)]

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

   (IndLT t1 t2) -> do
      unless (t1 `aeq` t2) $
             typeError"When using an inductive ordering with contra, must have a proof of the form 'x < x'"
                       [(text "The Expr",disp p),
                        (text "The Type",disp ty')]
      return ty

  where findCon (Con c) = Just c
        findCon (Pos _ t) = findCon t
        findCon (App t1 _ _) = findCon t1
        findCon _ = Nothing

-- ContraAbort

check ProofMode t@(ContraAbort taborts tterminates) (Just ty) = do
  aborts <- proofSynth' taborts
  terminates <- proofSynth' tterminates
  case (down aborts,down terminates) of
    (Equal abrt s, Terminates s')
      | isAbort abrt -> do
       ensure (down s `aeq` down s') $
                "Can't use contrabort'" <++> s <++> "' doesn't match '" <++>
                s' <++> "'"
       return ty



    _ -> typeError "Contraabort requires a proof of divergence and a proof of termination."
                 [(text "The term", disp t)
                 ,(text "The 'abort' term", disp taborts)
                 ,(text "The inferred type of the abort term", disp aborts)
                 ,(text "The 'terminates' term", disp tterminates)
                 ,(text "The inferred type of the terminates term", disp terminates)
                 ]

  where isAbort (Pos _ t) = isAbort t
        isAbort (Abort _) = True
        isAbort _ = False


check ProgMode (Abort t) expected = do
  typeAnalysis' t Type
  t `sameType` expected
  return t

check m (Show t) expected = do
  ty <- check m t expected
  emit $ ("We have the following classification:\n" $$$ t $$$ " : " $$$ ty)
  return t


-- Conv

-- ConvCtx
check mode (ConvCtx p ctx) expected = do
  unless (okCtx ctx) $
   typeError "In conv context, an explicit equality is used in an unerased position"
     [(text "The context", disp ctx)]

  ensure (mode `elem` [ProofMode,ProgMode]) $
         "Can't do conversion in mode" <++> show mode
  let submode = case mode of
                  ProofMode -> PredMode
                  ProgMode -> ProgMode
                  _ -> error "Unreachable case in check of ConvCtx def."

  -- lhs <- withErrorInfo "LHS Check" [(text "The context", disp ctx)] $
  --        withEscapeContext LeftContext $ check submode ctx Nothing
  -- emit "LHS is:"
  -- emit $ disp lhs


  l <- withErrorInfo "LHS escCopy" [(text "the context", disp ctx)] $ copyEqualInEsc LeftContext ctx
  -- emit $ "l is" <++> disp l


  withErrorInfo "When checking the left hand side of a context." [] $
                  check mode p (Just l)
  withErrorInfo
           "When checking the left hand side of a context."
           [(text "The context", disp l)] $
              withEscapeContext LeftContext $ check submode l Nothing
  r <- copyEqualInEsc RightContext ctx
  rty <- withErrorInfo  "When checking the right hand side of a context."
           [(text "The context", disp r)] $
              withEscapeContext RightContext $ check submode r Nothing
  r `sameType` expected
  return r


-- Ord

check ProofMode (Ord w) (Just ty@(IndLT l r)) = do
  -- Skeleton version of the 'ord' axiom.
  ty' <- proofSynth' w
  let errlist = [(text "the equality", disp ty') , (text "the expected ordering constraint", disp ty)]
  case down ty' of
    e@(Equal l' r') -> do
        let (c,ls) = splitApp' l'
        unless (r `aeq` r') $
          typeError ("In an ord-proof, the right-hand side of the equality proved by the subproof of ord does "
                     ++ "not match the right-hand side of the expected ordering constraint.")
            errlist
        let iscon (Con _) = True
            iscon _ = False
        unless (iscon c) $
          typeError ("In an ord-proof, the left-hand side of the equality proved by the subproof of ord "
                     ++ "is not an application of a constructor to arguments")
            errlist
        unless (any (aeq l) ls) $
          typeError ("In an ord-proof, the left-hand side of the expected ordering constraint does "
                     ++ "not appear as an argument in the application on the left-hand side of the equality proof"
                     ++ "proved by the subproof of ord.")
            errlist
        return ty
    _ -> typeError "In an ord-proof, the subproof of ord does not prove an equation."
           errlist

-- IndLT

check PredMode (IndLT t0 t1) expected = do
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
  let clean m = (\((n,Embed ty,inf),t) -> ((n,Embed (down ty),inf),down t)) <$> m
  (p1@(fun,_,witness),_) <- unbind prfBinding
  (a1,Forall predBinding') <- clean $ unbind predBinding

  ((f,tele,u),prfBody) <- unbind prfBinding
  (args,rest) <- pairTelePrf tele res


  case (reverse args, down rest) of
    ((iarg,iargTy,iInf):rargs,Forall predBody) -> do
      -- FIXME: Check to make sure targ == Terminates iarg
      ((targ,Embed tyTArg',predInf),predBody) <- unbind predBody
      let xvar = Var iarg
          y = string2Name "y"
          yvar = Var y
          fty = foldr (\(n,ty,inf) r -> Forall (bind (n,Embed ty,inf) r))
                      (Forall (bind (u,Embed (IndLT yvar (Var iarg)),False)
                              (subst iarg yvar predBody)))
                      (reverse ((y,iargTy,False):rargs))

      extendBinding f fty True $
        foldr (\(arg,ty,_) m -> extendBinding arg ty False m)
            (extendBinding u (Terminates xvar) True $
              check ProofMode prfBody (Just predBody))
            args
    _ -> typeError ("FIXME: Figure out a good error message for" <++>
                     "when an ind doesn't take a termination argument.")
                     []

  return res


-- Rec


check ProgMode r@(Rec progBinding) (Just res@(Pi piStage piBinding)) = do -- Term_Rec
  let pairTele tele (Pos _ t) = pairTele tele t
      pairTele Empty body = return ([],body)
      pairTele (TCons teleBinding) (Pi stage binding) = do
        ((piName,Embed piTy,piInf),piBody) <- unbind binding
        let ((teleName,teleStage,Embed teleTy,teleInf),rest) = unrebind teleBinding
        piMode <- getClassification piTy
        check (classToMode piMode) piTy Nothing
        teleMode <- getClassification teleTy
        check (classToMode teleMode) teleTy Nothing


        unless (teleTy `aeq` piTy) $
               typeError ("The type ascribed to a Rec-bound variable does not" <++>
                         "the type ascribed to the associated Pi bound variable")
               [(text "The Rec argument type", disp teleTy)
               ,(text "The Pi argument type", disp piTy)
               ,(text "The Rec expression", disp r)
               ,(text "The Pi expression", disp res)]
        (args,body') <- extendBinding teleName teleTy False $
                         pairTele rest (subst piName (Var teleName) piBody)
        return ((teleName,teleTy):args,body')

  -- FIXME: Surely some check on the stage is needed.
  ((f,tele),recBody) <- unbind progBinding
  (args,range) <- pairTele tele res
  -- emit $ "Rec type" <++> res
  -- unless(down ty `aeq` down piTy) $ typeError
  --   ("Type ascribed to a lambda-bound variable does not match the type" <++>
  --    "ascribed to the associated pi-bound variable")
  --   [(text "Lambda-variable type", disp ty)
  --   ,(text "Pi-variable type", disp piTy)]


  extendBinding f res True $
    foldr (\(arg,ty) m -> extendBinding arg ty True m)
            (typeAnalysis' recBody range) args
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
        _ -> typeError ("In strict context, witness of abort" <++>
                         "equality is not of the type 'abort = t'")
               [(text "The term",disp t)
                ,(text "The inferred type", disp ty)]



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
           let ty' = Equal (Abort cty) (f e2)
           ty' `sameType` expected
           return ty'
        _ -> throwError $ strMsg
               "In strict, the context hole is not of the proper form abort = e"


-- Sym
check mode (Sym t) expected = do
  ensure (mode `elem` [ProgMode, ProofMode]) $
         "Can't check sym in mode" <++> show mode
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

-- Refl
check mode Refl (Just ty) =
  let err =
        "The type expected for a refl-proof is not of the form t = t.\n\n"
        <++> "1. the type: "<++> ty in
  do
    case down ty of
      (Equal t0 t1) -> do
        ensure (t0 `aeq` t1) $ err
        return ty
      _ -> die $ err
    return ty



check mode (Trans t1 t2) expected = do
  ty1@(Equal a b) <- checkEqual mode t1
  ty2@(Equal b' c) <- checkEqual mode t2
  withErrorInfo "" [(text "The first equality", disp ty1),
                    (text "The second equality", disp ty2)] $ do
  case fmap down expected of
    Just (Equal ty0 ty1) -> do
       ensure (a `aeq` ty0) $
                "When checking a trans, the LHS of first equality" $$$
                a $$$ "does not match the LHS of the expected type." $$$
                ty0
       ensure (c `aeq` ty1) $
                "When checking a trans, the RHS of second equality" $$$
                c $$$ "does not match the RHS of the expected type" $$$
                ty1
    Nothing -> return ()

  ensure (b `aeq` b') $
             "When checking a trans, the RHS of first equality" $$$
             b $$$ "does not match the LHS of the second equality" $$$
             b'

  return (Equal a c)

    -- _ -> die $ "The type expected for a refl-proof is not an equation." $$$
    --              "1. the type: "<++> ty



-- Existentials
check PredMode (Exists binding) expected = do
  ((n,Embed ty),body) <- unbind binding
  check ProgMode ty (Just Type)
  extendBinding n ty False $ check PredMode body (Just (Formula 0))
  return (Formula 0)

check ProofMode (EElim scrutinee binding) (Just pred) = do
  stype <- check ProofMode scrutinee Nothing
  case down stype of
    (Exists ebinding) -> do
        ((n,Embed ty),epred) <- unbind ebinding

        -- Is this necessary?
        check ProgMode ty (Just Type)
        extendBinding n ty False $ check PredMode epred (Just (Formula 0))

        ((n',p),body) <- unbind binding
        extendBinding n' ty False $
          extendBinding p (subst n (Var n') epred) False $
            check ProofMode body (Just pred)


    _ -> typeError "Scrutinee of exists elim must be an existential."
         [(text "Inferred type", disp stype)]

check ProofMode (EIntro p1 p2) (Just res@(Exists ebinding)) = do
  ((n,Embed ty),epred) <- unbind ebinding
  check ProgMode ty (Just Type)
  extendBinding n ty False $ check PredMode epred (Just (Formula 0))

  check ProgMode p1 (Just ty)
  check ProofMode p2 (Just (subst n p1 epred))
  return res


check mode term expected = checkUnhandled mode term expected

checkUnhandled mode term expected = do
  typeError  "Unhandled typechecking case."
          [(text "mode", text $ show mode)
          ,(text "term", disp term)
          ,(text "expected",disp expected)]


checkEqual mode term = do
  ty <- check mode term Nothing
  case down ty of
    dty@(Equal a b) -> return dty
    _ -> die $ "Expecting an equality type." $$$
               "When checking the term" $$$ term $$$
               "and the type" $$$ ty $$$ "was inferred."



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
  where ((n,Embed ty,_),body) = unsafeUnbind binding
isLK _ = False


isPred (Var x) = True
isPred (Lambda Form Static binding) = isA ty && isPred body
  where ((n,Embed ty),body) = unsafeUnbind binding
isPred (App t0 Static t1) = isPred t0 && is_a t1
isPred (Forall binding) = isB ty && isPred body
  where ((n,Embed ty,_),body) = unsafeUnbind binding
isPred (Equal t0 t1) = isTerm t0 && isTerm t1
isPred (IndLT t0 t1) = isTerm t0 && isTerm t1
isPred (Terminates t) = isTerm t
isPred (Exists binding) = isA ty && isPred body
  where ((n,Embed ty),body) = unsafeUnbind binding
isPred (Ann p t) = isPred p && isLK t
isPred (Pos _ t) = isPred t

isPred _ = False


isProof (Var x) = True
isProof (Lambda Form  Static binding) = isB ty && isProof body
  where ((n,Embed ty),body) = unsafeUnbind binding
-- NOTE: This used to require that the annotation be 'static', but that didn't
-- work out, because we don't annotate stages on proof applications.
isProof (App t0 _ t1) = isProof t0 && is_b t1
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

-- FIXME: Checking the telescope is not quite right.
isProof (Ind binding) = isTermTele tele &&  isProof body
  where ((f,tele,opf),body) = unsafeUnbind binding
isProof (Contra p) = isProof p
isProof (ContraAbort p0 p1) = isProof p0 && isProof p1
isProof (Ann p pred) = isProof p && isPred pred
isProof (Pos _ t) = isProof t
isProof t = False



isTerm (Var _) = True
isTerm (Con _) = True
isTerm Type = True
isTerm (Pi _ binding) = isA ty && isTerm body
  where ((n,Embed ty,_),body) = unsafeUnbind binding
isTerm (Lambda Program _ binding) = isA ty && isTerm body
  where ((n,Embed ty),body) = unsafeUnbind binding
isTerm (ConvCtx t p) = isTerm t  -- Do we need to do anything with p?
isTerm (Conv t ts binding) = isTerm t &&
                             and [is_q t | t <- ts] &&
                             isTerm body
  where (_,body) = unsafeUnbind binding
isTerm (App t0 _ t1) = isTerm t0 && is_a t1
isTerm (Abort t) = isTerm t
isTerm (Rec binding) = isTermTele tele &&  isTerm body
  where ((f,tele),body) = unsafeUnbind binding

isTerm (Ann t0 t1) = isTerm t0 && isTerm t1
isTerm (Pos _ t) = isTerm t
isTerm (Escape t) = isTerm t
isTerm (Case t tbang binding) =  isTerm t && maybe True isTerm tbang
   where (n,alts) = unsafeUnbind binding
         altsOk = and [isTerm body | alt <- alts, ((_,_),body) <- [unsafeUnbind alt]]
isTerm (TCast t p) = isTerm t && isProof p

isTerm t = False

isTermTele Empty = True
isTermTele (TCons rebinding) = isTerm ty && isTermTele rest
  where ((_,_,Embed ty,_),rest) = unrebind rebinding


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
  unless (p t) $
         typeError "The expression is not of the proper syntactic class."
                   [(text "The expression", disp t)
                   ,(text "The class", text (show  cls))]



-- Placeholder for op. semantics
join lSteps rSteps t1 t2 = do
  -- emit $ "Joining" $$$ t1 $$$ "and" $$$ t2
  -- s1 <- substDefs t1
  -- s2 <- substDefs t2
  t1' <- withErrorInfo "While evaluating the first term given to join." [(text "The term", disp t1)]
           $ eval lSteps t1
  t2' <- withErrorInfo "While evaluating the second term given to join." [(text "The term", disp t2)]
           $ eval rSteps t2
  -- Top level definitions cause problems with alpha equality. Try to subsitute
  -- those in...
  s1 <- substDefsErased t1'
  s2 <- substDefsErased t2'

  unless (s1 `aeq` s2) $
         typeError "Terms are not joinable."
                   [(text "LHS steps", integer lSteps)
                   ,(text "RHS steps", integer rSteps)
                   ,(text "Original LHS", disp t1)
                   ,(text "Original RHS", disp t2)
                   ,(text "Reduced LHS", disp t1')
                   ,(text "Reduced RHS", disp t2')
                   ,(text "Substituted LHS", disp s1)
                   ,(text "Substituted RHS", disp s2)
                   ]

  return (Equal t1 t2)
  -- unless (t1 `aeq` t2) $ err "Terms not joinable"




-- Get the classification of a classifier (Type,Predicate,LogicalKind)
data Sort = SortType | SortPred | SortLK deriving (Eq,Show)
getClassification (Pos _ t) = getClassification t
getClassification t = do
   -- emit $ "Checking classification" <++> t
   res <- (ta `catchError` (\te ->
           pa `catchError` (\pe ->
           la `catchError` (\le -> do
             emit te
             emit pe
             emit le
             typeError "Cannot classify an expression."
                                   [(text "The expression", disp t)]))))
   -- emit $ "Classification is" <++> (show res)
   return res

  where ta = typeAnalysis' t Type >> return SortType
        pa = do -- emit $ "Checking if " <++> t <++> "is a pred."
                sort <- predSynth' t
                -- emit $ "Got a sort" <++> show sort
                unless (isLK (down sort)) $ err "Not a predicate"
                return SortPred
        la = do unless (isLK t) (err "Could not classify classifier")
                return SortLK


classToMode SortType = ProgMode
classToMode SortPred = PredMode
classToMode SortLK = error "classToMode: No case for SortLK"

-----------------------------------------------
-- Generic function for copying a term and
-- handling the escape clause in a specific manner
-- escCopy :: (Expr -> TCMonad Expr) -> Expr -> TCMonad Expr
-- escCopy f t = everywhereM (mkM f') t
--   where f' (Escape t) = f t
--         f' t = return t

-- escCopy' b (Escape (Equal l r)) =
--   case b of
--     LeftContext -> return l
--     RightContext -> return r
--     _ -> throwError $ strMsg $ "Copy can't reach this."
-- escCopy' b (Escape t) = do
--   ty <- withErrorInfo "When checking a proof of an equality in an escape."
--               [(text "The term", text $ show t)] $ proofSynth' t
--   case down ty of
--     (Equal l r) ->
--        case b of
--          LeftContext -> return l
--          RightContext -> return r
--          _ -> throwError $ strMsg $ "Copy can't reach this."
--     _ -> typeError "Can't escape to something not an equality."
--                [(text "The proof type", disp ty)]
-- escCopy' b
escCopy f (Escape e) = do
  e' <- escCopy f e
  f e'

escCopy f t@(Var _) = return t
escCopy f t@(Con _) = return t
escCopy f t@(Formula _) = return t
escCopy f Type = return Type
escCopy f (Pi st binding) = do
   ((n,Embed ty,inf),body) <- unbind binding
   ty' <- escCopy f ty
   body' <- escCopy f body
   return $ Pi st (bind (n,Embed ty',inf) body')
escCopy f (Forall binding) = do
   ((n,Embed ty,inf),body) <- unbind binding
   ty' <- escCopy f ty
   body' <- escCopy f body
   return $ Forall (bind (n,Embed ty',inf) body')
escCopy f (App e1 st e2) = do
  e1' <- escCopy f e1
  e2' <- escCopy f e2
  return $ App e1' st e2'
escCopy f (Lambda kind st binding) = do
   ((n,Embed ty),body) <- unbind binding
   ty' <- escCopy f ty
   body' <- escCopy f body
   return $ Lambda kind st (bind (n,Embed ty') body')
escCopy f (Case s term binding) = do
  s' <- escCopy f s
  (n,alts) <- unbind binding
  alts' <- mapM cpyAlt alts
  return $ Case s' term (bind n alts')
  where cpyAlt alt = do
          ((c,vars),body) <- unbind alt
          body' <-  escCopy f body
          return $ bind (c,vars) body'
escCopy f (TerminationCase e binding) = do
  e' <- escCopy f e
  (n,(a,bang)) <- unbind binding
  a' <- escCopy f a
  bang' <- escCopy f bang
  return $ TerminationCase e' (bind n (a',bang'))
escCopy f t@(Join _ _) = return t
escCopy f (Equal l r) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ Equal l' r'
escCopy f (Val e) = do
  e' <- escCopy f e
  return $ Val e'
escCopy f (Terminates e) = do
  e' <- escCopy f e
  return $ Terminates e'
escCopy f (Contra e) = do
  e' <- escCopy f e
  return $ Contra e'
escCopy f (ContraAbort l r) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ ContraAbort l' r'
escCopy f (Abort e) = do
  e' <- escCopy f e
  return $ Abort e'
escCopy f (Show e) = do
  e' <- escCopy f e
  return $ Show e'
escCopy f (Conv e ps binding) = do
  e' <- escCopy f e
  (holes,ctx) <- unbind binding
  ctx' <- escCopy f ctx
  return $ Conv e' ps (bind holes ctx')
escCopy f (ConvCtx l r) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ ConvCtx l' r'
escCopy f (IndLT l r) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ IndLT l' r'
escCopy f (OrdTrans l r) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ OrdTrans l' r'
escCopy f (Ind binding) = do
  ((n,tele,ord),body) <- unbind binding
  body' <- escCopy f body
  tele' <- escCopyTele f tele
  return $ Ind (bind (n,tele',ord) body')
escCopy f (Rec binding) = do
  ((n,tele),body) <- unbind binding
  body' <- escCopy f body
  tele' <- escCopyTele f tele
  return $ Rec (bind (n,tele') body')
escCopy f (Let binding) = do
  ((n,eq,Embed val),body) <- unbind binding
  val' <- escCopy f val
  body' <- escCopy f body
  return $ Let (bind (n,eq,Embed val') body')
escCopy f (Aborts e) = do
  e' <- escCopy f e
  return $ Aborts e'
escCopy f (Sym e) = do
  e' <- escCopy f e
  return $ Sym e'
escCopy f Refl = return Refl
escCopy f (Trans l r) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ Trans l' r'
escCopy f (MoreJoin ps) = do
  ps' <- mapM (escCopy f) ps
  return $ MoreJoin ps
escCopy f (Ann l r) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ Ann l' r'
escCopy f (Pos p e) = do
  e' <- escCopy f e
  return $ Pos p e'
escCopy f (TCast l r) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ TCast l' r'



escCopyTele f Empty = return Empty
escCopyTele f (TCons rebinding) = do
    e' <- escCopy f e
    rest' <- escCopyTele f rest
    return $ TCons (rebind (n,st,Embed e',inf) rest')
  where ((n,st,Embed e,inf),rest) = unrebind rebinding



copyEqualInEsc b x = escCopy f x
 where f (Equal l r) = case b of
                         LeftContext -> return l
                         RightContext -> return r
                         _ -> throwError $ strMsg $ "Copy can't reach this."


       f (Pos p t) =  f t
       f t  = do ty <-
                  withErrorInfo "When checking a proof of an equality in an escape."
                     [(text "The term", disp t)] $ proofSynth' t
                 case down ty of
                  (Equal l r) ->
                     case b of
                       LeftContext -> return l
                       RightContext -> return r
                       _ -> throwError $ strMsg $ "Copy can't reach this."
                  _ -> typeError "Can't escape to something not an equality."
                       [(text "The proof type", disp ty)]




checkCaseCoverage tyS alts = do
    -- Checking constructor coverage
    let (tc,args) = splitApp' tyS
    (tele,cs) <- case down tc of  -- declared (constructor, arity)
                   (Con tcName) -> lookupTypeCons tcName
                   _ -> die $ "Can't find type constructor" <++> show tc

    altCs <- forM alts (\a -> do { ((n,vars),_) <- unbind a;
                                   return (string2Name n, length vars)})

    let unhandled =  (nub $ map fst cs) \\ (nub $ map fst altCs)
    ensure (null unhandled) $
           "Unhandled constructors:" <++> (vcat $ map disp unhandled)

    let teleSub =  subTele tele args
    cs<- forM altCs (\(n,arity) ->
                  case lookup n cs of
                    Nothing -> die $ n <++> "is not a constructor of" <++> tc
                    Just (arity',ty)
                      | arity == arity' -> return (n,teleSub ty)
                      | otherwise -> die $ "Pattern arity" <++> arity <++>
                                     "does not match constructor" <++> n <++>
                                                          "arity" <++> arity')
    return $ (args,cs)








pairTele tele (Pos _ t) = pairTele tele t
pairTele Empty body = return ([],body)
pairTele (TCons teleBinding) (Pi stage binding) = do
        ((piName,Embed piTy,piInf),piBody) <- unbind binding
        let ((teleName,teleStage,Embed teleTy,teleInf),rest) = unrebind teleBinding
        piMode <- getClassification piTy
        check (classToMode piMode) piTy Nothing
        teleMode <- getClassification teleTy
        check (classToMode teleMode) teleTy Nothing
        unless (teleTy `aeq` piTy) $
               typeError ("The type ascribed to a Rec-bound variable does not" <++>
                         "the type ascribed to the associated Pi bound variable")
               [(text "The Rec argument type", disp teleTy)
               ,(text "The Pi argument type", disp piTy)]
        (args,body') <- extendBinding teleName teleTy False $
                         pairTele rest (subst piName (Var teleName) piBody)
        return ((teleName,teleTy):args,body')
pairTele tele ps = typeError (show tele ++ "\n" ++ show ps) []

-- Given a telescope representing a series of bindings, and a (nested) Forall
-- formula, pair up the bindings in the telesope with the bindings in the formula.
pairTelePrf tele (Pos _ t) = pairTelePrf tele t
pairTelePrf Empty body = return ([],body)
pairTelePrf (TCons teleBinding) (Forall binding) = do
        ((piName,Embed piTy,piInf),piBody) <- unbind binding
        let ((teleName,teleStage,Embed teleTy,teleInf),rest) = unrebind teleBinding
        piMode <- getClassification piTy
        check (classToMode piMode) piTy Nothing
        teleMode <- getClassification teleTy
        check (classToMode teleMode) teleTy Nothing

        unless (teleTy `aeq` piTy) $
               typeError ("The type ascribed to a Rec-bound variable does not" <++>
                         "the type ascribed to the associated Pi bound variable")
               [(text "The Rec argument type", disp teleTy)
               ,(text "The Pi argument type", disp piTy)]
        (args,body') <- extendBinding teleName teleTy False $
                         pairTelePrf rest (subst piName (Var teleName) piBody)
        return ((teleName,teleTy,teleInf):args,body')






-- * Implicit arguments.


implicit mode t expected = do

  (f,actuals) <- unroll t []
  -- let (stages,args) = unzip actuals

  fTy <- check mode f Nothing
  -- Calculate an initial substitution.
  (iSub,indices) <- initialSub fTy actuals [] expected

  (ty,vars,sub) <- loop fTy (0,indices) [] actuals iSub

  -- emit $ "Final Sub" $$$ show vars
  -- emit $ "Resulting type" <++> ty
  ty `sameType` expected
  return ty
  where -- unroll the application, return the function applied and the arguments
        unroll (Pos _ t) acc = unroll t acc
        unroll (App f s x) acc = unroll f ((s,x):acc)
        unroll t acc = return (t,acc)


        -- process the arguments w.r.t. the type.
        -- arguments:
        --    (idx,imap) the number of quantifiers crossed and a mapping between indices and variables in sub
        --    vars, metavars
        --    args, actual arguments to the application
        --    sub, the cumulative substitution
        loop (Pos p t) ix vars args sub = loop t ix vars args sub `catchError` addErrorPos p t
        loop piTy@(Pi piStage binding) (idx,imap) vars args@((argStage,a):as) sub = do


          ((n,Embed dom,inf),body) <- unbind binding
          let Just old = lookup idx imap -- The variable name in the initial substitution
          -- There has to be a better way to do the substitution.
          let sub' = swapNames (single (AnyName n) (AnyName old)) sub
          if inf
             -- The the argument is to be inferred, then we check to see if we already have
             -- an instantiation as an input.
            then do
               case lookupMatch n sub' of
                 Just ty' -> do
                   check mode ty' (Just dom)
                   loop (subst n ty' body) (idx + 1,imap) vars args sub
                 Nothing -> do
                   loop body (idx+1,imap) ((n,dom,piStage):vars) args sub
            else do
                 -- Get the sort of the argument type, so we can check it in the correct mode.
                 cls <- getClassification dom
                 argMode <- case cls of
                     SortPred -> return ProofMode
                     SortType -> return ProgMode
                     _ -> typeError ("The classifier of the argument to a programmatic application" <++>
                                    "should either be a predicate or program.")
                                    [(text "FIXME: Reconstruct term", disp a),
                                     (text "The classifier", disp dom)]

                 -- See if there are any metavariables in the expected type. If there are, then we have
                 -- to synthesize a type, because we can't check on uninstantiated metavars.
                 let argType = isInstantiated [v | (v,_,_) <- vars] dom

                 aTy <- check argMode a argType

                 when (mode == ProgMode) $ do
                    withErrorInfo "The argument type does not have the syntactic classification A."
                           [(text "The argument", disp a)] $  requireA aTy


                 -- when (mode ==  ProofMode) $ do
                 --      ensure (constrApp term) $ term <++> "is not a construction."

                 unless (piStage == argStage) $ do
                   typeError "The stage for the arrow does not match the stage for the application"
                       [(text "Arrow stage:",disp piStage),
                        (text "Application stage", disp argStage)]




                 newSub <- match [n | (n,_,_) <- vars] dom aTy
                 nextSub <- extendMatch n a =<< extendMatches newSub sub'

                 let body' = applyMatch nextSub body
                 loop body' (idx + 1,imap) vars as sub'

        loop piTy@(Forall binding) (idx,imap) vars args@((argStage,a):as) sub = do
          ((n,Embed dom,inf),body) <- unbind binding
          let Just old = lookup idx imap
          let sub' = swaps (single (AnyName old) (AnyName n)) sub
          if inf
             then do
               case lookupMatch n sub' of
                 Just ty' -> do
                   check mode ty' (Just dom)
                   loop (subst n ty' body) (idx + 1,imap) vars args sub
                 Nothing -> loop body (idx+1,imap) ((n,dom,Static):vars) args sub
             else do
                 -- See if there are any metavariables in the expected type. If there are, then we have
                 -- to synthesize a type, because we can't check on uninstantiated metavars.
                 let argExpected = isInstantiated [v | (v,_,_) <- vars] dom
                 aTy <- check mode a argExpected
                 newSub <- match [n | (n,_,_) <- vars] dom aTy
                 nextSub <- extendMatch n a =<< extendMatches newSub sub'
                 let body' = applyMatch nextSub body


                 when (mode == PredMode) $ guardLK body
                 when (mode == ProofMode) $ do
                     requireB aTy
                     requirePred body

                 loop body' (idx + 1,imap) vars as nextSub


        loop ty idx vars [] sub = return (ty,vars,sub)
        loop t  idx vars ((_,a):as) sub =
            typeError "Trying to apply a term that is not a quantification"
                        [(text "The type", disp t), (text "The arg", disp a)]



-- | initialSub calculates the initial substitution for an application based on
-- the expected type of the application. Because 'unbind' gives a fresh name to
-- the variables in the pattern, we can't directly use those names later when
-- inferring arguments. To get around this issue, we assign indices (with 0
-- being the outermost binding), which we will then use when looking up
-- variables.
initialSub ty args vars Nothing = return (emptyMatch,[])
initialSub (Pos _ t) args vars  expected = initialSub t args vars expected
initialSub (Pi _ binding) args@(a:as) vars expected
    | inf = initialSub body args (n:vars) expected
    | otherwise = initialSub body as (n:vars) expected
  where ((n,_,inf),body) = unsafeUnbind binding
initialSub (Forall binding) args@(a:as) vars expected
    | inf = initialSub body args (n:vars) expected
    | otherwise = initialSub body as (n:vars) expected
  where ((n,_,inf),body) = unsafeUnbind binding

initialSub ty [] vars (Just expected) = do
  subst <- match vars ty expected
  let idxs = [(i,v) | i<- [0..] | v <- reverse vars]
  return (subst,idxs)

initialSub ty args _ (Just expected) =
  typeError "Can't calculate initial substitution."
              ([(text "The input type", disp ty)
              ,(text "The expected type", disp expected)] ++
              [(text "Argument", disp a) | (_,a) <- args])
