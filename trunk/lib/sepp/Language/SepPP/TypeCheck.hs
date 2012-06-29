{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables,
TemplateHaskell, RankNTypes #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Language.SepPP.TypeCheck(typecheck) where

import Language.SepPP.Syntax
import Language.SepPP.PrettyPrint
import Language.SepPP.Eval
import Language.SepPP.TCUtils
import Language.SepPP.Options

import Unbound.LocallyNameless hiding (Con,isTerm,Val,join,Equal,Refl,findCon)

import Unbound.LocallyNameless.Ops(unsafeUnbind)

import qualified Generics.RepLib as RL

import Text.PrettyPrint

-- import Data.Typeable

import "mtl" Control.Monad.Reader hiding (join)
import "mtl" Control.Monad.Error hiding (join)
import "mtl" Control.Monad.State hiding (join)

import Control.Applicative
import Text.Parsec.Pos
import Data.List(nubBy, find,findIndex)
import qualified Data.Set as S

typecheck :: Module -> IO (Either TypeError ())
typecheck modul = do
  runErrorT $ runFreshMT $ runReaderT (evalStateT (runTCMonad (typecheckModule modul)) flagMap) emptyEnv

-- * Running the typechecker.

-- | Typecheck an entire module
typecheckModule :: Module -> TCMonad ()
typecheckModule (Module _ decls) = do
    checkDefs decls
    return ()
  where checkDefs [] = return ()
        checkDefs (d:ds) = do
          env <- checkDef d
          local (combEnv env) $ checkDefs ds


-- | Typecheck a single definition
checkDef :: Decl -> TCMonad Env
checkDef (FlagDecl nm b) = do
  setFlag nm b
  return emptyEnv

checkDef (OperatorDecl _nm _level _fixity) =
  return emptyEnv

checkDef (AxiomDecl nm theorem) = do
  emit $ "Checking axiom" <++> nm
  lk <- predSynth' theorem
  isLK <- lkJudgment lk
  ensure isLK ("Theorem is not a well-formed logical kind " <++> nm)
  return $ extendEnv nm theorem False emptyEnv


checkDef (ProofDecl nm theorem proof) = do
  emit $ "Checking proof" <++> nm
  lk <- predSynth' theorem
  emit $ "Resulting logical kind is" <++> lk
  isLK <- lkJudgment lk
  ensure isLK ("Theorem is not a well-formed logical kind " <++> nm)
  proofAnalysis' proof theorem

  return $ extendEnv nm theorem False emptyEnv

checkDef (ProgDecl nm ty prog) = do
  emit $ "Checking program" <++> nm
  typeAnalysis' ty Type
  typeAnalysis' prog ty
  _isVal <- synValue prog
  return $ extendDef nm ty prog False emptyEnv

checkDef (DataDecl (Con nm) binding) = do
  emit $ "Checking data type" <++> nm
  (tele,cs) <- unbind binding

  -- Turn the telescope (from the type arguments to the type
  -- constructor) into a dependent product.
  let ty = teleArrow tele Type

  -- Make sure that the type constructor is a well-formed type.
  withErrorInfo "When checking that a type constructor is kindable."
                [(text "The Type Constructor", disp nm)
                ,(text "The Type",disp ty)] $
      typeAnalysis' ty Type


  -- Change the erasure annotations of all type args to runtime using dynArrow.
  conTypes <- extendBinding nm (dynArrow ty) True $
              extendTele tele $ (mapM chkConstructor cs)

  let env = extendEnv nm (dynArrow ty) True $
              foldr (\(cnm,(_arity,ty')) env' ->
                      extendEnv cnm (teleArrow tele ty') True env')
              (extendTypes nm tele conTypes emptyEnv)
              conTypes
  return env

  where chkConstructor :: (EName,Expr) -> TCMonad (EName,(Int,Expr))
        chkConstructor (c,ty) = do
          typeAnalysis' ty Type
          (args,ran) <- unrollPi ty
          case unrollApp ran of
             (Con tc, _) -> do
               unless (tc == nm) $
                 typeError "Constructor range type doesn't match data type."
                   [(disp "The type", disp nm),
                    (disp "The data constructor", disp tc),
                    (disp "The actual range type", disp ran)
                    ]
               return (c,(length args,ty))
             (h,_) -> do
               die $ "Constructor head is" <++> h
checkDef (DataDecl expr _) = do
  typeError "A data declaration must only be named with a constructor name."
             [(disp "The name", disp expr)]


checkDef (EvalStmt expr) = do
  ty <- check ProgMode expr Nothing
  res <- eval 10000 expr
  emit $ ">" $$$ expr <++> ":" <++> ty $$$ "> reduces to" $$$ res

  return emptyEnv
  

-- * Judgements on proof fragment

-- The S,G |- LK : LogicalKind judgment
lkJudgment :: Expr -> TCMonad Bool
lkJudgment (Formula _ ) = return True
lkJudgment (Forall binding) = do
  ((n,Embed ty,_inf),body) <- unbind binding
  requireA ty
  extendBinding n ty False (lkJudgment body)

lkJudgment (Pos _ t) = lkJudgment t
lkJudgment t = do
  typeError "Could not classify term as a logical kind"
            [(text "The Expr", disp t)]


data CheckMode = LKMode | PredMode | ProofMode | ProgMode | NoMode deriving (Show,Eq)

check :: CheckMode -> Expr -> Maybe Expr -> TCMonad Expr
check mode (Pos p t) expect  = check mode t expect `catchError` addErrorPos p t
check mode t (Just (Pos _ expect)) = check mode t (Just expect)

-- check mode (Ann t ty) Nothing = check mode t (Just ty)
check mode (Ann t ty) expected = do
  ret <- check mode t (Just ty)
  sameType ty expected
  return ret


check NoMode t Nothing = do
  mode <- synClass t
  -- emit $ "Moving to mode" <++> show mode <++> "for" <++> t
  check (toMode mode) t Nothing

check NoMode t (Just expected) = do
  mode <- synClass t
  check (toMode mode) t (Just expected)



-- Var
check _mode (Var n) expected = do
  (ty,_) <- lookupBinding n
  ty `sameType` expected
  return ty

-- Con
check ProgMode (Con t) expected = do
  (ty,_) <- lookupBinding t
  ty `sameType` expected
  return ty


-- Formula

-- Type
check ProgMode Type Nothing = return Type
check ProgMode Type (Just Type) = return Type -- Expr_Type
check mode Type _ =
  typeError "Can't check Type in non-programmatic mode."
    [(disp "The mode", disp $ show mode)]

-- Pi

check ProgMode tm@(Pi stage binding) expected = do -- Expr_Pi
  ((n,Embed ty,_inf),body) <- unbind binding
  cls <- synClass ty
  case cls of
    ProgClass -> return ()
    PredClass -> do
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

check _mode tm@(Pi _ _) ty = do
  die $ "Can't check Pi type in non-programmatic mode." $$$
        tm $$$
        ty


-- Forall
check PredMode quant@(Forall binding) Nothing = do
  ((n,Embed t,_inf),body) <- unbind binding

  case down t of
    Formula i -> do  -- Pred_Forall3 rule
           form <- extendBinding n t False (predSynth' body)
           (Formula j) <- guardFormula form
           return (Formula (max (i+1) j))
    -- (Forall binding') -> do -- Pred_Forall4 rule
    --   emit $ "guardLK" <++> t
    --   sc <- synClass t
    --   emit  $ "class" <++> (show sc)
    --   guardLK t
    --   form <- extendBinding n t False (predSynth' body)
    --   guardFormula form

    dom -> do
      cls <- synClass dom
      case cls of
        PredClass -> do  -- Pred_Forall1
          lk <- predSynth' dom
          case lk of
            Formula _ -> do
                    extendBinding n dom False (predSynth' body)
            _ -> do
                typeError "predSynth pred case, not a formula."
                  [(disp "The classifier", disp lk)]
        ProgClass -> do
                 ty <- typeSynth' t
                 ty `expectType` Type
                 form <- extendBinding n t False (predSynth' body)
                 guardFormula form
        LKClass -> do
          emit "LKClass"
          fail "miserably"
        ProofClass -> typeError "The classifier of a quantifier cannot be a proof."
                      [(disp "The quantifier" , disp quant)
                      ,(disp "The classifier", disp dom)]

  where guardFormula t@(Formula _) = return t
        guardFormula t = typeError "Not a formula" [(disp "The expression", disp t)]

check mode form@(Forall _) _ = do
  typeError "Can't check Forall formula in non-predicate mode."
    [(disp "The formula", disp form)
    ,(disp "The mode", disp $ show mode)]

-- App
check mode (App t0 stage t1) expected = do
  ty0 <- check mode t0 Nothing
  case down ty0 of
    Pi piStage binding -> do
      ((x,Embed dom,_inf),body) <- unbind binding
      check NoMode t1 (Just dom)
      unless (piStage == stage) $ do
        typeError "The stage for the arrow does not match the stage for the application"
          [(text "Arrow stage:",disp piStage),
           (text "Application stage", disp stage)]

      let ran = subst x t1 body
      ran `sameType` expected
      return ran
    Forall binding -> do
      ((x,Embed dom,_inf),body) <- unbind binding
      check NoMode t1 (Just dom)
      let ran = subst x t1 body
      ran `sameType` expected
      return ran
    _ -> typeError "When checking an application, the term being applied is not a pi or forall type."
         [(disp "The term", disp t0),
          (disp "The type", disp ty0)
         ]

-- Lambda

check PredMode (Lambda Form Static binding) Nothing = do -- Pred_Lam rule
  ((n,Embed ty),body) <- unbind binding
  -- First Premise
  requireW ty
  -- Second Premise
  form <- extendBinding n ty False (predSynth' body)
  lk <- lkJudgment form
  ensure lk $ form <++> " is not a valid logical kind."
  return (Forall (bind (n,Embed ty,False) form))

check ProofMode (Lambda Form _ pfBinding)
              (Just out@(Forall predBinding)) = do -- Prf_Forall.
  Just ((proofName,Embed pfTy),pfBody,(_predName,Embed _predTy,_predInf),predBody) <-
    unbind2 pfBinding predBinding

  pfKind <- check NoMode pfTy Nothing
  requireQ pfKind
  extendBinding proofName pfTy False (proofAnalysis' pfBody predBody)
  return out


check ProgMode (Lambda Program progStage progBinding) (Just (Pi piStage piBinding)) = do
  unless (progStage == piStage) $
         typeError "When checking a lambda-term against a pi-type, the stage annotations do not match."
                   [(text "The Lambda stage annotation", disp $ show progStage)
                   ,(text "The Pi stage annotation", disp $ show piStage)
                   ]

  Just ((progName,Embed progTy), progBody,(_piName,Embed _piTy,_piInf), piBody) <-
    unbind2 progBinding piBinding
  -- TODO: Several side conditions on stage annotations
  extendBinding progName progTy True $ typeAnalysis' progBody piBody


check ProgMode (Lambda Program stage binding) Nothing = do
  ((nm,Embed ty),body) <- unbind binding
  bodyTy <- extendBinding nm ty True $ check ProgMode body Nothing
  return $ Pi stage (bind (nm,Embed ty,False) bodyTy)

-- Case
check mode t@(Case s pf binding) expected = do
  (sEq,alts) <- unbind binding
  tyS <- typeSynth' s

  -- Checking termination proof
  case (mode,pf) of
    (ProofMode,Just termProof) -> do
      proofAnalysis' termProof (Terminates s)
      return ()
    (ProofMode, Nothing) ->
        typeError "When case-splitting in a proof, a termination proof must be supplied."
         [(disp "The case expression", disp t)]
    (ProgMode, Just _) ->
        typeError
          "When checking a case expression in program mode, no termination proof should be supplied."
          []
    (ProgMode, Nothing) -> return ()
    _ -> typeError "Case expressions can only be checked in proof or prog mode."
         [(disp "The mode", disp $ show mode)]

  case unrollApp tyS of
    (Con tc, args) -> do
      -- Coverage check.
      (_,constructors) <- lookupTypeCons tc
      let dataCons, altCons :: S.Set EName
          dataCons = S.fromList $ map fst constructors
          altCons = S.fromList [string2Name $ fst $ fst $ unsafeUnbind alt | alt <- alts]

      unless (dataCons == altCons) $
         typeError "Case patterns don't match data constructors."
           [(disp "The type constructor", disp tc)
           ,(disp "Unhandled constructor", cat (map disp $ S.toList (dataCons S.\\ altCons)))
           ,(disp "Extraneous patterns ", cat (map disp $ S.toList (altCons S.\\ dataCons)))
           ]


      -- Typecheck each alternative.
      let chkAlt alt = do
            -- Get the data constructor's type
            ((cons,vars),body) <- unbind alt
            (consTy,_) <- lookupBinding (string2Name cons)

            (consArgs,_) <- unrollPi consTy
            -- Split into a 'telescope' for type constructor args, and
            -- a 'telescope' for type constructor args
            let (_,conArgsFormal) = splitAt (length args) consArgs

            -- Check that we have the right # of pattern variables.
            unless (length vars == length conArgsFormal) $ do
               typeError "Wrong number of pattern variables for constructor"
                  [(disp "The constructor", disp cons)]

            -- Build a big substitution, substituting actual type
            -- arguments for formal type arguments, and pattern
            -- variables for the remaining data constructor arguments.
            let to :: [Expr]
                to = map fst args ++ map (Var . fst) vars -- Type arguments, followed by pattern variables
                from :: [EName]
                from = [n | (n,_,_,_) <- consArgs] -- Formal parameters
                sub = substs (zip from to)

            let eq :: Expr
                eq = Equal (sub $ rollApp (Con (s2n cons)) [(Var n,stage) | (n,stage,_,_) <- consArgs])
                           s

            -- makes sure that pattern variable stage annotations match formal stage annotation
            let chkStage :: (EName,Stage) -> (EName,Stage,a,b) -> TCMonad ()
                chkStage (pvar,pstage) (n,nstage,_,_) =
                   unless (pstage == nstage) $ 
                      typeError "Pattern variable stage does not match constructor argument stage"
                        [(disp "The constructor", disp cons)
                        ,(disp "The formal parameter", disp n)
                        ,(disp "The pattern variable", disp pvar)]


            sequence $ zipWith chkStage vars conArgsFormal

 
            -- Build a typing environment
            let penv = [(pvar,sub ty)| (pvar,_) <- vars | (_,_,ty,_) <- conArgsFormal]

            -- Check the body of the branch
            aty <- foldr (\(v,ty) m -> extendBinding v ty True m) 
                     (extendBinding sEq eq True (check mode body expected)) penv
     

            -- Make sure that the compile-time pattern variables (and the name of the equality proof)
            -- do not occur free in the erasure.
            when (mode == ProgMode) $ do
               bodyVars :: S.Set EEName <- fv <$> erase body
               let compileVars :: S.Set EEName = S.fromList [translate n | (n,Static) <- vars]
               let evars  = compileVars `S.intersection` bodyVars
               unless (S.null evars) $ do
                 typeError "The erased pattern variables appear free in a case alternative."
                     [(disp "The vars", cat $ punctuate comma (map disp (S.toList evars)))]
               return ()
            return aty

      -- Make sure all branches have the same type.
      atys <- mapM chkAlt alts

      case nubBy aeq atys of
        [] -> maybe (typeError "Can't infer a type for a case expression with no branches." []) return expected
        [l] -> return l
        ls -> typeError "Types of case alternatives do not match"
                   [(disp $ "Type" ++ (show (i::Int)), disp typ) | i <- [0..] | typ <- ls]

    (h,_args) -> typeError "Could not unroll an application to a constructor."
                    [(disp "The head", disp h)]

-- TerminationCase
check mode t@(TerminationCase s binding) expected = do
  unless (mode `elem` [ProofMode, ProgMode]) $
         typeError "Termination case is not valid in this mode."
                     [(text "The term", disp t)
                     ,(text "The mode", disp $ show mode)]
  sty <- typeSynth' s
  (w,(abort,terminates)) <- unbind binding
  ty1 <- extendBinding w (Equal (Abort sty) s) True (check mode abort expected)
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
check mode t@(Tactic (MoreJoin ps)) (Just eq@(Equal t0 t1)) = do
  unless (mode `elem` [ProofMode,ProgMode]) $
     typeError "Morejoin is only valid in proof and programming mode."
               [(text "The Term", disp t)
               ,(text "The Mode", disp $ show mode)]
  (rs,ts) <- checkProofs ps
  withErrorInfo "When evaluating with rewrite rules, while checking a morejoin proof." []
    $ withTermProofs ts $ withRewrites rs (join 10000 10000 t0 t1)
  return eq

  where checkProofs [] = return ([],[])
        checkProofs (q:qs) = do
          ty <- withErrorInfo "When checking a proof supplied to morejoin." [ (text "The proof", disp q)] $
                  check ProofMode q Nothing
          case down ty of
            Equal t1' t2' -> do
              et1 <- erase t1'
              et2 <- erase t2'
              (rs,ts) <- checkProofs qs
              return ((et1,et2):rs,ts)

            Terminates tm -> do
                (rs,ts) <- checkProofs qs
                t' <- erase tm
                return (rs,t':ts)

            other -> typeError
                    ("Term does not have the correct type to be used as a morejoin rewrite." <++>
                    "It must either be a equality or termination proof.")
                      [(text "The Expr", disp q),
                       (text "The Type", disp other)]


-- Equal
check PredMode (Equal t0 t1) _expected = do
  ty0 <- typeSynth' t0
  ty1 <- typeSynth' t1
  typeAnalysis' ty0 Type
  typeAnalysis' ty1 Type
  return (Formula 0)

-- Val
check ProofMode (Val x) expected = do
     let f t = do ty <- typeSynth' t
                  case down ty of
                   (Terminates subject) -> return subject
                   _ -> typeError "Can't escape to something not a Termination in valCopy."
                          [(disp "The expression", disp ty)]
     term <- escCopy f x
     typeSynth' term
     stub <- escCopy (\_ -> return Type) x
     b <- synValue stub
     if b
        then do let ans = Terminates (down term)
                ans `sameType` expected
                return ans
        else typeError "Can't judge a term a value."
                         [(disp "The term", disp x)]

check mode (TCast t p) expected = do
  ty <- check mode t expected
  check ProofMode p (Just (Terminates t))
  return ty

-- Terminates
check mode (Terminates t) expected = do -- Pred_Terminates rule
  ensure (mode `elem` [PredMode,ProgMode]) $
           "Can't check type of Terminates term in " <++> show mode <++> "mode."
  _ty <- typeSynth' t
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
          unless (c1 /= c2) $
            typeError "In contra, constructors must be unique."
              [(disp "First constructor", disp c1)
              ,(disp "Second constructor", disp c2)]
          return ty
       _ -> do
         typeError "In contra, equality proof must be between constructor values."
           [(disp "The formula", disp ty')]

   (IndLT t1 t2) -> do
      unless (t1 `aeq` t2) $
             typeError"When using an inductive ordering with contra, must have a proof of the form 'x < x'"
                       [(text "The Expr",disp p),
                        (text "The Type",disp ty')]
      return ty
   _ -> typeError "When using contra, the supplied proof must either equate distinct construtors or be a reflexive ordering."
        [(disp "The term", disp tm)
        ,(disp "The type", disp ty')]

  where findCon (Con c) = Just c
        findCon (Pos _ t) = findCon t
        findCon (App t1 _ _) = findCon t1
        findCon _ = Nothing

-- ContraAbort
check ProofMode t@(ContraAbort taborts tterminates) (Just ty) = do
  aborts <- proofSynth' taborts
  terminates <- proofSynth' tterminates
  case (down aborts,down terminates) of
    (Equal s1 s2, Terminates s')
      | isAbort s1 -> do
         unless (down s2 `aeq` down s') $
           typeError "Can't use contraabort, because terms don't match."
             [(text "The term equated with abort.", disp s2),
              (text "The term proved terminating.", disp s')
             ]
         return ty

    _ -> typeError "Contraabort requires a proof of divergence and a proof of termination."
                 [(text "The term", disp t)
                 ,(text "The 'abort' term", disp taborts)
                 ,(text "The inferred type of the abort term", disp aborts)
                 ,(text "The 'terminates' term", disp tterminates)
                 ,(text "The inferred type of the terminates term", disp terminates)
                 ]
  where isAbort (Pos _ tm) = isAbort tm
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
  _rty <- withErrorInfo  "When checking the right hand side of a context."
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
    (Equal l' r') -> do
        let (c,ls) = unrollApp l'
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
        unless (any (aeq l) (map fst ls)) $
          typeError ("In an ord-proof, the left-hand side of the expected ordering constraint does "
                     ++ "not appear as an argument in the application on the left-hand side of the equality proof"
                     ++ "proved by the subproof of ord.")
            errlist
        return ty
    _ -> typeError "In an ord-proof, the subproof of ord does not prove an equation."
           errlist

-- IndLT
check PredMode (IndLT t0 t1) _expected = do
  typeSynth' t0
  typeSynth' t1
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
check ProofMode tm@(Ind prfBinding) (Just res@(Forall predBinding)) = do -- Prf_Ind
  -- FIXME: This is a hack, because there are different number of binders in the
  -- Ind and Forall forms.
  let clean m = (\((n,Embed ty,inf),t) -> ((n,Embed (down ty),inf),down t)) <$> m
  -- (p1@(fun,_,witness),_) <- unbind prfBinding
  (_,Forall _predBinding') <- clean $ unbind predBinding

  ((f,tele',u),prfBody) <- unbind prfBinding


  let pairTelePrf tele (Pos _ t) = pairTelePrf tele t
      pairTelePrf Empty body = return ([],body)
      pairTelePrf (TCons teleBinding) (Forall binding) = do
        ((piName,Embed piTy,_piInf),piBody) <- unbind binding
        let ((teleName,_teleStage,Embed teleTy,teleInf),rest) = unrebind teleBinding
        check NoMode piTy Nothing
        check NoMode teleTy Nothing
        -- piMode <- getClassification piTy
        -- check (classToMode piMode) piTy Nothing
        -- teleMode <- getClassification teleTy
        -- check (classToMode teleMode) teleTy Nothing

        unless (teleTy `aeq` piTy) $
               typeError ("The type ascribed to a Rec-bound variable does not" <++>
                         "the type ascribed to the associated Pi bound variable")
               [(text "The Rec argument type", disp teleTy)
               ,(text "The Pi argument type", disp piTy)]
        (args,body') <- extendBinding teleName teleTy False $
                         pairTelePrf rest (subst piName (Var teleName) piBody)
        return ((teleName,teleTy,teleInf):args,body')
      pairTelePrf _tele _body = typeError "Can't unroll ind form with expected type."
                               [(disp "The term", disp tm)
                               ,(disp "The expected type", disp res)]

  (args,rest) <- pairTelePrf tele' res
  case (reverse args, down rest) of
    ((iarg,iargTy,_iInf):rargs,Forall predicate) -> do
      -- FIXME: Check to make sure targ == Terminates iarg
      ((_targ,Embed _tyTArg',_predInf),predBody) <- unbind predicate
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


check ProgMode r@(Rec progBinding) (Just res@(Pi _ _)) = do -- Term_Rec
  let pairTele tele (Pos _ t) = pairTele tele t
      pairTele Empty body = return ([],body)
      pairTele (TCons teleBinding) (Pi _stage binding) = do
        ((piName,Embed piTy,_piInf),piBody) <- unbind binding
        let ((teleName,_teleStage,Embed teleTy,_teleInf),rest) = unrebind teleBinding
        check NoMode piTy Nothing
        check NoMode teleTy Nothing
        -- piMode <- getClassification piTy
        -- check (classToMode piMode) piTy Nothing
        -- teleMode <- getClassification teleTy
        -- check (classToMode teleMode) teleTy Nothing


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
      pairTele _tele _ty  = do
        typeError "Rec form must have a pi type."
           [(disp "The rec form", disp r)
           ,(disp "The expected type", disp res)]
          
          

  -- FIXME: Surely some check on the stage is needed.
  ((f,tele),recBody) <- unbind progBinding
  (args,range) <- pairTele tele res
  extendBinding f res True $
    foldr (\(arg,ty) m -> extendBinding arg ty True m)
            (typeAnalysis' recBody range) args
  return res

-- Escape
check _mode (Escape t) _expected = do
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
check mode (Let _stage binding) expected = do
    unless (mode `elem` [ProofMode,ProgMode]) $
           die $ "Let expressions cannot be checked in" <++> show mode <++> "mode."
    ((n,pf,Embed t),body) <- unbind binding

    ty' <- check NoMode t Nothing

    -- In proofs, programmatic abbreviations are not values
    cls <- synClass ty'
    let isVal = case mode of
          ProofMode -> cls /= ProgClass
          ProgMode -> True
          LKMode -> False
          NoMode -> False
          PredMode -> False


    extendBinding n ty' isVal $
     maybe id (\pf' -> extendBinding pf' (Equal (Var n) t) True) pf $
     check mode body expected

-- Existentials
check PredMode (Exists binding) _expected = do
  ((n,Embed ty),body) <- unbind binding
  check ProgMode ty (Just Type)
  extendBinding n ty False $ check PredMode body (Just (Formula 0))
  return (Formula 0)

check ProofMode (EElim scrutinee binding) (Just expected) = do
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
            check ProofMode body (Just expected)


    _ -> typeError "Scrutinee of exists elim must be an existential."
         [(text "Inferred type", disp stype)]


check ProgMode (EElim scrutinee binding) expected = do
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
            check ProgMode body expected
    _ -> typeError "Scrutinee of exists elim must be an existential."
         [(text "Inferred type", disp stype)]



check ProofMode (EIntro p1 p2) (Just res@(Exists ebinding)) = do
  ((n,Embed ty),epred) <- unbind ebinding
  check ProgMode ty (Just Type)
  extendBinding n ty False $ check PredMode epred (Just (Formula 0))
  check ProgMode p1 (Just ty)
  check ProofMode p2 (Just (subst n p1 epred))
  return res




-- Aborts

check ProofMode (Aborts c) expected = withEscapeContext StrictContext $ do
  emit $ "Checking context" <++>  c
  cty <- typeSynth' c
  case isStrictContext c of
    Nothing -> throwError $ strMsg "Not a strict context"
    Just (e,f) -> do
      eqTy <- typeSynth' e
      case down eqTy of
        (Equal (Abort _) e2) -> do
           let ty' = Equal (Abort cty) (f e2)
           ty' `sameType` expected
           return ty'
        _ -> throwError $ strMsg
               "In strict, the context hole is not of the proper form abort = e"


-- Sym
check mode (Tactic (Sym t)) expected = do
  ensure (mode `elem` [ProgMode, ProofMode]) $
         "Can't check sym in mode" <++> show mode
  ty <- check ProofMode t Nothing
  case down ty of
    (Equal t1 t0)-> do
      let ty' = (Equal t0 t1)
      ty' `sameType`  expected
      return ty'
    _  ->
       typeError "Sym's argument must have the type of an equality proof."
        []

-- Refl
check _ (Tactic Refl) (Just ty) = do
    case down ty of
      (Equal t0 t1) -> do
        unless (t0 `aeq` t1) $
          typeError "The type expected for a refl proof is not of the form t = t."
             [(disp "The expected type", disp ty)]
        return ty
      _ ->  typeError "The type expected for a refl proof is not an equality formula."
              [(disp "The expected type", disp ty)]

    return ty




check mode (Tactic (Trans t1 t2)) expected = do
  ty1@(Equal a b) <- checkEqual mode t1
  ty2@(Equal b' c) <- checkEqual mode t2
  withErrorInfo "" [(text "The first equality", disp ty1),
                    (text "The second equality", disp ty2)] $ do

    unless (b `aeq` b') $
        typeError ("When checking a trans, the RHS of the first equality does not" ++
                      "match the LHS of the second equality.")
            [(disp "RHS of first equality", disp b),
             (disp "LHS of expected type", disp b')]
    
    case fmap down expected of
      Just (Equal lhs rhs) -> do
        unless (a `aeq` lhs) $
          typeError ("When checking a trans, the LHS of first equality does not" ++
                     "match the LHS of the expected type.")
            [(disp "LHS of first equality", disp (show a)),
             (disp "LHS of expected type", disp (show lhs))]
        unless (c `aeq` rhs) $
          typeError ("When checking a trans, the RHS of the second equality does not" ++
                      "match the LHS of the expected type.")
            [(disp "RHS of second equality", disp (show c)),
             (disp "RHS of expected type", disp (show rhs))]

      Just res ->
        typeError "When checking a trans equality, the expected type is not an equality"
          [(disp "The expected type", disp res )]
      Nothing -> return ()

  ensure (b `aeq` b') $
             "When checking a trans, the RHS of first equality" $$$
             b $$$ "does not match the LHS of the second equality" $$$
             b'

  return (Equal a c)

check mode (Tactic (Equiv depth)) (Just expect@(Equal lhs rhs)) = do
  pfs <- equate depth
  -- ctx <- asks gamma
  -- let eqprfs = [(Var n,downAll t) | (n,(t,_)) <- ctx]
  --     start = concat [[(n,ty),(Sym n, Equal t2 t1)] |  (n,ty@(Equal t1 t2)) <- eqprfs]
  --     pfs = iterate step start !! (fromIntegral depth)
  case find (\(_,ty) -> ty `aeq` expect) pfs of
    Just (n,_) -> do
      emit $ "Found  proof of" <++> expect <++> "as" <++> n
      check mode n (Just expect)
    Nothing -> typeError "Equiv"
               ([(disp "LHS", disp lhs)
               ,(disp "RHS", disp rhs)
               ] ++
               [(disp n, disp ty) | (n,ty) <- pfs])

check mode (Tactic (Autoconv tm)) (Just expected) = do
  ty <- check mode tm Nothing
  eqprfs <- equate 2
  ctx <- same eqprfs (downAll ty) (downAll expected)
  let tm' = ConvCtx tm ctx
  emit $  "Autoconv works with" <++> tm'
  check mode tm' (Just expected)


check _ t@(Tactic (Injective _)) Nothing = do
  typeError "Can't synthesize a type for the injective tactic. Ascribe a result type."
     [(disp "The expression", disp t)]
     
check mode (Tactic (Injective consEq)) (Just resEq) = do
  emit $ "Proving injectivity of"  <++> resEq <++> "using" <++> consEq
  res <- injective consEq resEq
  check mode res (Just resEq)



check mode term expected = 
  typeError  "Unhandled typechecking case."
          [(text "mode", text $ show mode)
          ,(text "term", disp term)
          ,(text "expected",disp expected)]


checkEqual :: CheckMode -> Expr -> TCMonad Expr
checkEqual mode term = do
  ty <- check mode term Nothing
  case down ty of
    dty@(Equal _ _) -> return dty
    _ -> die $ "Expecting an equality type." $$$
               "When checking the term" $$$ term $$$
               "and the type" $$$ ty $$$ "was inferred."



predSynth' :: Expr -> TCMonad Expr
predSynth' t = check PredMode t Nothing

proofSynth' :: Expr -> TCMonad Expr
proofSynth' t = check ProofMode t Nothing

proofAnalysis' :: Expr -> Expr -> TCMonad Expr
proofAnalysis' t ty = check ProofMode t (Just ty)

typeSynth' :: Expr -> TCMonad Expr
typeSynth' t = check ProgMode t Nothing


typeAnalysis' :: Expr -> Expr -> TCMonad Expr
typeAnalysis' t ty = check ProgMode t (Just ty)


data SynClass = LKClass | PredClass | ProofClass | ProgClass deriving (Show,Eq)

toMode :: SynClass -> CheckMode
toMode LKClass = LKMode
toMode PredClass = PredMode
toMode ProofClass = ProofMode
toMode ProgClass = ProgMode


synClass :: Expr -> TCMonad SynClass
synClass (Con _) = return ProgClass
synClass Type = return ProgClass
synClass (Pi _ _) = return ProgClass
synClass (TCast _ _) = return ProgClass
synClass (Abort _) = return ProgClass
synClass (Rec _) = return ProgClass

synClass (Conv subject _ _) = synClass subject
synClass (ConvCtx subject _) = synClass subject

synClass (App f _ _) = synClass f
synClass (Lambda Form _ _) = return ProofClass
synClass (Lambda Program _ _) = return ProgClass
synClass (Case _ (Just _) _) = return ProofClass
synClass (Case _ Nothing _) = return ProgClass

synClass (TerminationCase _ _) = return ProofClass
synClass (Join _ _) = return ProofClass
synClass (Val _) = return ProofClass
synClass (Contra _) = return ProofClass
synClass (ContraAbort _ _) = return ProofClass
synClass (Ord _) = return ProofClass
synClass (OrdTrans _ _) = return ProofClass
synClass (Ind _) = return ProofClass
synClass (EIntro _ _) = return ProofClass
synClass (EElim _ _) = return ProofClass
synClass (Aborts _) = return ProofClass
synClass (Tactic (Sym _)) = return ProofClass
synClass (Tactic (Equiv _)) = return ProofClass
synClass (Tactic Refl) = return ProofClass
synClass (Tactic (Trans _ _)) = return ProofClass
synClass (Tactic (Autoconv t)) = synClass t
synClass (Tactic (MoreJoin _)) = return ProofClass
synClass (Tactic (Injective _)) = return ProofClass

synClass WildCard = fail "Can't take the syntactic class of a wildcard!"
synClass (Ann e _) = synClass e
synClass (Pos _ e) = synClass e

-- This should *never* be invoked, since escapes can only appear in
-- conversion contexts, and we don't ever look at the context when
-- doing syntactic classification.
synClass (Escape _) = return ProofClass

synClass (Equal _ _) = return PredClass
synClass (Terminates _) = return PredClass
synClass (IndLT _ _) = return PredClass
synClass (Exists _) = return PredClass

synClass (Formula _) = return LKClass -- could be lkclass?
synClass (Forall binding) = do
  ((_,Embed _,_),body) <- unbind binding
  synClass body
--                       return PredClass -- could be lkclass?

synClass (Show e) = synClass e
synClass (Var v) = do
  (ty,_) <- lookupBinding v
  cls <- synClass ty
  return $ downOne cls
  where downOne LKClass = PredClass
        downOne PredClass = ProofClass
        downOne ProofClass = error $ "Can't classify with a proof"
        downOne ProgClass = ProgClass


synClass t = typeError "Can't classify the syntactic category of an expression."
             [(disp "The expression", disp t)]


requireA :: Expr -> TCMonad ()
requireA t = do
  cls <- synClass t
  unless (cls `elem` [ProgClass,PredClass]) $
    typeError "Term is not is the A syntactic class of programs or predicates."
    [(disp "The term", disp t),
     (disp "Acutal syntactic class", disp $ show cls)
    ]


requireQ :: Expr -> TCMonad ()
requireQ Type = return ()
requireQ (Formula _) = return ()
requireQ (Pos _ t) = requireQ t
requireQ t = do
  cls <- synClass t
  unless (cls == LKClass) $
     typeError "Term is not is the Q syntactic class"
      [(disp "The term", disp t),
       (disp "Acutal syntactic class", disp $ show cls)
      ]


requireW :: Expr -> TCMonad ()
requireW (Formula _) = return ()
requireW (Pos _ t) = requireW t
requireW t =
  typeError "Term is not is the W syntactic class"
      [(disp "The term", disp t)]



join :: Integer -> Integer -> Expr -> Expr -> TCMonad Expr
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

  unless (s1 `aeq` s2 || t1' `aeq` t2') $ do
         showRewrites
         typeError "Terms are not joinable."
                   [(text "LHS steps", integer lSteps)
                   ,(text "RHS steps", integer rSteps)
                   ,(text "Original LHS", disp t1)
                   ,(text "Original RHS", disp t2)
                   ,(text "Reduced LHS", disp t1')
                   ,(text "Reduced RHS", disp t2')
                   ,(text "Reduced LHS Raw", disp (show t1'))
                   ,(text "Reduced RHS Raw", disp ( show t2'))
                   ,(text "Substituted LHS", disp s1)
                   ,(text "Substituted RHS", disp s2)
                   ]

  return (Equal t1 t2)


escCopy ::  (Expr -> TCMonad Expr) -> Expr -> TCMonad Expr
escCopy f (Escape e) = do
  e' <- escCopy f e
  f e'
escCopy _ t@(Var _) = return t
escCopy _ t@(Con _) = return t
escCopy _ t@(Formula _) = return t
escCopy _ Type = return Type
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
escCopy _ t@(Join _ _) = return t
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
escCopy f (Let stage binding) = do
  ((n,eq,Embed val),body) <- unbind binding
  val' <- escCopy f val
  body' <- escCopy f body
  return $ Let stage (bind (n,eq,Embed val') body')
escCopy f (Aborts e) = do
  e' <- escCopy f e
  return $ Aborts e'
escCopy f (Tactic (Sym e)) = do
  e' <- escCopy f e
  return $ Tactic (Sym e')
escCopy _ (Tactic Refl) = return $ Tactic Refl
escCopy f (Tactic (Trans l r)) = do
  l' <- escCopy f l
  r' <- escCopy f r
  return $ Tactic $ Trans l' r'
escCopy f (Tactic (MoreJoin ps)) = do
  ps' <- mapM (escCopy f) ps
  return $ Tactic $ MoreJoin ps'
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
escCopy f (Ord p) = Ord <$> escCopy f p
escCopy f (Exists binding) = do
  ((n,Embed ty),body) <- unbind binding
  ty' <- escCopy f ty
  body' <- escCopy f body
  return (Exists (bind (n,Embed ty') body'))
escCopy _ t = typeError "EscCopy not defined." [(disp "The expression", disp t)]
  


escCopyTele :: (Expr -> TCMonad Expr) -> Tele -> TCMonad Tele
escCopyTele _ Empty = return Empty
escCopyTele f (TCons rebinding) = do
    e' <- escCopy f e
    rest' <- escCopyTele f rest
    return $ TCons (rebind (n,st,Embed e',inf) rest')
  where ((n,st,Embed e,inf),rest) = unrebind rebinding



copyEqualInEsc :: EscapeContext -> Expr -> TCMonad Expr
copyEqualInEsc b x = escCopy f x
 where f (Equal l r) = case b of
                         LeftContext -> return l
                         RightContext -> return r
                         _ -> throwError $ strMsg $ "Copy can't reach this."
       f (Pos _ t) =  f t
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
       


-- Equational reasoning tactic
equate ::  Integer -> TCMonad [(Expr, Expr)]
equate depth = do
  ctx <- asks gamma
  let ctx' = [(Var n,downAll t) | (n,(t,_)) <- ctx]
      start = concat [[(n,ty),(Tactic (Sym n), Equal t2 t1)] |  (n,ty@(Equal t1 t2)) <- ctx']
      pfs = iterate step start !! (fromIntegral depth)
  return pfs
  where trans (t1,Equal l1 r1) (t2,Equal l2 r2)
          | l1 `aeq` r2 = []
          | r1 `aeq` l2  = [(Tactic $ Trans t1 t2, (Equal l1 r2))] -- , (Sym (Trans t1 t2), (Equal r2 l1))]
          | otherwise = []
        trans _ _ = []
        step cs = cs ++ concat [trans p1 p2 | p1 <- cs, p2 <- cs]



class (Rep1 SameD t, Rep t) => Same t where
  same :: (Monad m) => [(Expr,Expr)] -> t -> t -> m t
  same  = sameR1 rep1

instance Same t => Sat (SameD t) where
  dict = SameD same

instance (Same p, Same n) => Same (Bind p n)
instance (Same l, Same r) => Same (l,r)
instance (Same x, Same y, Same z) => Same (x,y,z)
instance (Same w, Same x, Same y, Same z) => Same (w,x,y,z)
instance Same Bool
instance Same t => Same (Embed t)
instance Same SourcePos
instance Same a => Same [a]
instance Same Stage
instance Same Tele
instance Same Kind
instance Same Integer
instance Same EName where
instance Same a => Same (Maybe a)
instance (Same a, Same  b) => Same (Rebind a b)
instance Same Char
instance Same Tactic
-- No idea why this is required...

instance (Same t) => Same (R t)

data SameD t =
  SameD {  sameD :: forall m . (Monad m) =>
                    [(Expr,Expr)] -> t -> t -> m t }

instance Same Expr where
  same pfs t1 t2
   | t1 `aeq` t2 = return t1
   | Just (pf,_) <- find rightProof pfs = return (Escape pf)
   -- TODO: Should also try to synthesize a proof using morejoin.
   | otherwise = sameR1 rep1 pfs t1 t2
   where rightProof (_,Equal t1' t2') = t1 `aeq` t1' && t2 `aeq` t2'
         rightProof (_,_) = False

sameR1 :: Monad m => R1 SameD t -> [(Expr,Expr)] -> t -> t -> m t
sameR1 Int1 _  x y  = unless (x == y) ( fail "miserably") >> return x
sameR1 Integer1 _ x y = unless (x == y) (fail "miserably") >> return x
sameR1 Char1 _  x y = unless (x == y) (fail "miserably") >> return x
sameR1 (Data1 _ cons) vars x y = loop cons x y where
   loop (RL.Con emb reps : rest) x' y' =
     case (from emb x', from emb y') of
       (Just p1, Just p2) -> do
         args <- same1 reps vars p1 p2
         return (to emb args)
       (Nothing, Nothing) -> loop rest x y
       (_,_)              -> fail "sameR1 Data1"
   loop [] _ _ = fail "same1 Data1(loop)"

sameR1 _ _ _ _ = fail "Could not match values."

same1 ::  Monad m => MTup SameD l -> [(Expr,Expr)] -> l -> l -> m l
same1 MNil _ Nil Nil = return Nil
same1 (r :+: rs) vars (p1 :*: t1) (p2 :*: t2) = do
  s1 <- sameD r vars p1 p2
  s2 <- same1 rs vars t1 t2
  return (s1 :*: s2)






-- | Injective tactic

-- This takes an equality between two data constructors: p : (C a0
-- ... an = C b0 ... bn) and generates a proof of (ai = bi),
-- identified by the second argument of the `injective` function.  The
-- general scheme is that it creates a projection function prj_i s.t.
-- prj_i (C t0 ... tn) = ti. Rather than top-level projection
-- functions, it creates these on the fly as `case (C t0 ... tn) {_}
-- of { C p0 ... pn -> pi | _ -> abort T}`, where T is the type of ti.
-- Using this, it generates `join : ai = prj_i (C a0 .. an)` and `p2:
-- prj_i (C b0 .. bn) = bi`.  Additionally, `conv refl = prj_i (C a0
-- .. an) = prj_i (~p)` gives `prj_i (C a0 .. an) = prj_i (C b0
-- .. bn)`. Transitivity yields `ai = bi`.

-- Injectivity only holds for runtime data constructor
-- arguments. Additionally, the terms (C a0 .. an) and (C b0 .. bn)
-- must be values (otherwise join won't step prj_i (C a0 ... an) to
-- ai).

-- This currently only works for non-dependent types, because the
-- tactic doesn't insert any of the necessary conversions in the
-- matching branch to get the branch to be the correct type (since the
-- type of the projected term will likely have free pattern variables
-- within it that need to be `conv`ed using proofs that are also
-- constructor arguments. It's possible this may be automated (e.g. by
-- adding injectivity itself to the proof methods used by equiv
-- tactic, which is in turn used by autoconv, and then wrappig the
-- projected pattern variable with an autoconv.
injective :: Expr -> Expr -> TCMonad Expr
injective consEq (Equal l' r') = do
  form@(Equal l r) <- down <$> check ProofMode consEq Nothing

  -- Check that both sides are the same constructor.
  let (lcon,lArgs) = unrollApp l
      (rcon,rArgs) = unrollApp r
      isCon (Con _) = True
      isCon _ = False
  unless (isCon (down lcon)) $
    typeError
       "Can't prove injectivity using a proof of an equation with a non-constructor on left-hand side."
          [(disp "The proof", disp consEq)
          ,(disp "of the formula", disp form)]

  unless (isCon (down rcon)) $
    typeError
      "Can't prove injectivity using a proof of an equation with a non-constructor on right-hand side."
          [(disp "The proof", disp consEq)
          ,(disp "of the formula", disp form)]

  unless (down lcon `aeq` down rcon) $ do
    typeError "Can't prove injectivity using a proof of an equation with dissimilar constructors."
          [(disp "The proof", disp consEq)
          ,(disp "of the formula", disp form)]


  -- Make sure the subterms occur in matching position. This needs to
  --  be expanded so that we can find multiple indices for
  -- repeated occurances of the same subterm.
  (idxl,idxr) <- case (findIndex (aeq l' . fst) lArgs, findIndex (aeq r' . fst) rArgs) of
      (Just a,Just b) 
        | a == b -> return (a,b)
        | otherwise ->
          typeError "The target subterms occur in different positions in the provided equality proof."
          [(disp "The proof", disp consEq)
          ,(disp "of the formula", disp form)
          ,(disp "Target LHS subterm position", disp a)
          ,(disp "Target RHS subterm position", disp b)]

      (Just _, Nothing) ->
        typeError "The target subterm could not be found in the RHS of the provided equality proof."
          [(disp "The proof", disp consEq)
          ,(disp "of the formula", disp form)
          ,(disp "Target RHS subterm", disp r')]

      (Nothing, Just _) ->
        typeError "The target subterm could not be found in the LHS of the provided equality proof."
          [(disp "The proof", disp consEq)
          ,(disp "of the formula", disp form)
          ,(disp "Target LHS subterm", disp l')]



      (Nothing, Nothing) ->
        typeError "The target subterms could not be found in the provided equality proof."
          [(disp "The proof", disp consEq)
          ,(disp "of the formula", disp form)
          ,(disp "Target LHS subterm", disp l')
          ,(disp "Target RHS subterm", disp r')]

    
  lhsType <- check ProgMode l Nothing
  rhsType <- check ProgMode r Nothing

  let (lTc,_) = unrollApp lhsType
      (rTc,_) = unrollApp rhsType

  unless (lTc `aeq` rTc) $ 
        typeError "The sides of the supplied equality do not seem to be of the same type constructor."
          [(disp "The proof", disp consEq)
          ,(disp "of the formula", disp form)
          ,(disp "LHS type constructor", disp lTc)
          ,(disp "RHS type constructor", disp rTc)]



  lType' <- check ProgMode l' Nothing
  rType' <- check ProgMode r' Nothing
  
  prjLeft <- mkCase (down lTc) lcon lType' idxl l
  prjRight <- mkCase (down rTc) rcon rType' idxr r

  contextRight <- mkCase (down lTc) lcon lType' idxl (Escape consEq)


  let u1 = Ann (Join 0 1000) (Equal l' prjLeft)

      -- l' = prj l
      u2 = Ann (Join 1000 0) (Equal prjRight r')
      -- prj r = r'
      casting = ConvCtx (Join 0 0) (Equal prjLeft contextRight)
      -- cast refl : prj l = prj l to prj l = prj r using l = r
      p1 =  (Ann (Tactic (Trans u1 casting)) (Equal l' prjRight))
      -- l' = prj r
      p2 = Tactic (Trans p1 u2)
      -- l' = r'
  emit $  "Injectivity tactic generated proof" <++> p2
  return p2

injective _ ty =
  typeError "The injective tactic can only prove an expected equality."
    [(disp "The expected type", disp ty)]
  
      


-- Note that we can only prove injectivity for positions that are not erased.



mkCase :: Expr -> Expr -> Expr -> Int -> Expr -> TCMonad Expr
mkCase (Con tc) (Con dc) dt idx scrutinee = do
  (tcTele,constructors) <- lookupTypeCons tc

  let numTypeParams = length $ fTele (:) [] tcTele
  
  alts <- mapM (mkAlt numTypeParams) constructors
  let expr = Pos tacticPosition $
       Case scrutinee Nothing  
                    (bind (s2n "_eq") alts)
  return expr
  where
    mkAlt :: Int -> (EName, (Int,Expr)) -> TCMonad (Bind (String,[(EName,Stage)]) Expr)
    mkAlt numTypeParams (c,(_,ty)) = do
        (piArgs,_) <- unrollPi ty
        let pstages = [stage | (_,stage,_,_) <- piArgs]
        pnames <- sequence $ [fresh (string2Name ("pvar_" ++ (name2String n))) | (n,_,_,_) <- piArgs]
        let pvars = zip pnames pstages
                    
        if c /= dc
           then return $ bind (name2String c,pvars) (Abort dt)
           else do
               let (prjVar,prjStage) = pvars !! (idx - numTypeParams)
               when (prjStage == Static) $
                 typeError
                    "When calculating a projection for injectivity reasoning, can't project a static argument."
                    []
               return $ bind (name2String c,pvars)  (Var prjVar)

mkCase tc dc _ _ _ = do
  typeError "mkCase in the injective tactic requires that both the type and data representations to be constructors. "
    [(disp "The type constructor representation", disp tc)
    ,(disp "The data constructor representation", disp dc)]

  




  