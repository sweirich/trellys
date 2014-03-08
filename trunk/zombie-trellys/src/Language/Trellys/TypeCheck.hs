{-# LANGUAGE ViewPatterns, TypeSynonymInstances, ExistentialQuantification, NamedFieldPuns, 
             ParallelListComp, FlexibleContexts, ScopedTypeVariables, TupleSections,
             FlexibleInstances #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | The Trellys surface language typechecker, using a bi-directional typechecking algorithm
-- to reduce annotations.
module Language.Trellys.TypeCheck
  (ta, tcModule, tcModules, emptyEnv)
where

import Language.Trellys.Syntax

import Language.Trellys.PrettyPrint(Disp(..))
import Language.Trellys.OpSem

import Language.Trellys.Options
import Language.Trellys.Environment
import Language.Trellys.Error
import Language.Trellys.TypeMonad
import Language.Trellys.EqualityReasoning
import Language.Trellys.TypeCheckCore
--import qualified Language.Trellys.TypeCheckCore as TypeCheckCore
--import Language.Trellys.TestReduction

import Generics.RepLib.Lib(subtrees)
import Text.PrettyPrint.HughesPJ

import Control.Applicative ((<$>))
import Control.Monad.Reader hiding (join)
import Control.Monad.Error  hiding (join)

import Language.Trellys.GenericBind

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S


{-
-- For debugging:
getType a = do
   liftIO $ putStrLn . render. disp $
      [ DS "getType of", DD a]
   result <- TypeCheckCore.getType a
   liftIO $ putStrLn "done"
   return result
aGetTh a = do
   liftIO $ putStrLn . render. disp $
      [ DS "aGetTh of", DD a]
   result <- TypeCheckCore.aGetTh a
   liftIO $ putStrLn "done"
   return result
aKc a = do
   liftIO $ putStrLn . render. disp $
      [ DS "aKc of", DD a]
   result <- TypeCheckCore.aKc a
   liftIO $ putStrLn "done"
   return result
-}

{-
  We rely on two mutually recursive judgements:

  * ta is an analysis judgement that takes a term and a type 
    and checks it.

  * ts is a synthesis that takes a term and synthesizes a type.

  Both functions also return an annotated term which is an
  elaborated version of the input term. The invariants for this is:

   - ta takes a source term and elaborated type, returns elaborated term
     - The elaborated type has already been kind-checked, 
       ta will not re-check it.
   - ts takes a source term, returns elaborated term and elaborated type.
     - The elaborated type is guaranteed to be well-kinded
  
  From the elaborated term, we can also recover the minimal theta 
  that makes that term typecheck. So these two functions also implicitly 
  compute th.

  In both functions, the context (gamma) is an implicit argument
  encapsulated in the TcMonad.  

  We maintain the following invariants wrt zonking:
    - The type argument of ta is already zonked when ta is called.
    - The values returned by ta and ts are zonked before they are returned.
    - The types in gamma are not yet zonked.
  -}


-- | kind check, for check = synthesis ?

-- Elaborate tm, and check that it is a well-formed type
-- at some level.
kcElab ::  Term -> TcMonad ATerm
kcElab tm = do
  (etm,ty) <- ts tm 
  case (eraseToHead ty) of
    AType _ -> return etm
    _       -> err [DD tm, DS "is not a well-formed type"]
--
-- Elaborate tm,  check that it is a well-formed first-order type
-- at some level, if it is not first-order but there is a specified 
-- default then use that default.
kcElabFirstOrder :: Term -> TcMonad ATerm
kcElabFirstOrder ty = do
  (ety,tyTy) <- ts ty
  dth <- getDefaultTheta
  case (eraseToHead tyTy, isFirstOrder ety, dth) of
    (AType _, True, _) -> 
      return ety
    (AType _, False, Nothing) ->
      err [DD ty, 
           DS  "can not be used as the domain of a function/data type, must specify either",
           DD (At ty Logic), DS "or", DD (At ty Program),
           DS "(no default theta is currently in effect.)"]
    (AType _, False, Just th) ->
      return (AAt ety th)
    (_, _, _)      -> 
      err [DD ty, DS "is not a well-formed type"]

isFirstOrder :: ATerm -> Bool
isFirstOrder (eraseToHead -> ATyEq _ _)    = True
isFirstOrder (eraseToHead -> ASmaller _ _) = True
isFirstOrder (eraseToHead -> AAt _ _)      = True
isFirstOrder (eraseToHead -> ATCon d _)    = True
isFirstOrder (eraseToHead -> AAt _ _)      = True
isFirstOrder (eraseToHead -> AType _)      = True
isFirstOrder _ = False

-- Check wellformedness of, and elaborate, each type in a telescope
kcTele :: Telescope -> TcMonad ATelescope
kcTele [] = return AEmpty
kcTele ((x,ty,ep):tele') = do
   ety <- kcElabFirstOrder ty
   etele' <- extendCtxSolve (ASig (translate x) Program ety) $ kcTele tele'
   return (ACons (rebind (translate x,embed ety,ep) etele'))

-- | Type analysis
-- Check that the provided term has the given type
-- Produce the corresponding annotated language term
ta :: Term -> ATerm -> TcMonad ATerm

-- Position terms wrap up an error handler
ta (Pos p t) ty =
  extendSourceLocation (Just p) t $
    ta  t ty

ta (Paren a) ty = ta a ty

ta (ComplexCase bnd) tyB = do
   (scruts, alts) <- unbind bnd
   let checkNumPats (ComplexMatch bnd1) = do
         (pats, body) <- unbind bnd1
         unless (length pats == length scruts) $
           err [ DS $"Each branch should have " ++ show (length scruts) ++ " patterns, but",
                 DD (ComplexMatch bnd1), DS $ "has " ++ show (length pats) ++  "."]
   mapM_ checkNumPats alts
   escruts <- mapM (\(s, eq) -> do                       
                       (es, sTy) <- ts (unembed s) 
                       return (es, eq))
                   scruts
   ztyB <- zonkTerm tyB
   buildCase escruts alts ztyB

-- implements the checking version of T_let1 and T_let2
ta (Let th' ep bnd) tyB =
 do -- begin by checking syntactic -/L requirement and unpacking binding
    when (ep == Erased && th' == Program) $
       err [DS "Implicit lets must bind logical terms."]
    ((x,y,unembed -> a),b) <- unbind bnd
    -- premise 1
    (ea,tyA) <- ts a
    eaTh <- aGetTh ea
    unless (eaTh <= th') $
      err [DS (show y ++ " was marked as " ++ show th' ++ " but"), 
           DD a, DS "checks at P"]
      
    -- premise 2
    (eb,th) <- extendCtx (ASig (translate x) th' tyA) $
                 extendCtxSolve (ASig (translate y) Logic 
                                (ATyEq (AVar (translate x)) ea)) $ do
                   eb <- ta b tyB
                   th <- aGetTh eb
                   return (eb,th)
    -- premise 3 (tyB is well-kinded) is assumed to be checked already.
    -- premises 4 and 5
    bE <- erase eb
    when (translate y `S.member` fv bE) $
      err [DS "The equality variable bound in a let is not allowed to",
           DS "appear in the erasure of the body, but here", DD y,
           DS "appears in the erasure of", DD b]
    when (ep == Erased && translate x `S.member` fv bE) $
      err [DS "The variables bound in an implicit let are not allowed to",
           DS "appear in the erasure of the body, but here", DD x,
           DS "appears in the erasure of", DD b]
    zea <- zonkTerm ea
    --The max enforces that P vars can not be bound in an L context.
    return (ALet ep (bind (translate x, translate y, embed zea) eb) 
            (max th th', tyB))

-- rule T_At
ta (At ty th') (AType i) = do 
   ea <- ta ty (AType i)
   eaTh <- aGetTh ea
   unless (eaTh == Logic) $
     err [DD ty, DS "should check at L but checks at P"]
   return (AAt ea th')

{- Type inference for @-types (the T_Box* rules) does not work super well.
   @-types are so ubiquitous that if we used some syntactic mark in the program
   (e.g. (box a), like we do in the pretty-printed core terms), all terms would
   be really cluttered. So instead we try to put them in guided by the 
   bidirectional types, which works kindof poorly (in particular it is not
   clear how to do an "up-to-congruence" search without some term constructor
   to trigger it.

   It is important that the following two clauses come before the
   checking rules for functions or equations, because a term was
   ascribed an @-type we want to immediately do the TBox, rather than
   e.g. search for a function type equivalent to that @-type...  

   On the other hand, it should come after the Tcase and Tlet rules so
   that we don't overcomit to a box too early... This is very brittle.
   -}

-- Horrible hack to avoid applying Box* too eagerly.
-- The bidirectional inference of box seems dubious, will need
-- to revisit this.
ta a (AAt tyA th') | unCheckable a = do
  (ea, tyA') <- ts a
  eaTh <- aGetTh ea
  isVal <- isValue a
  withoutBox <- coerce ea tyA' (AAt tyA th')
  case withoutBox of
    Just eaCoerced -> return $ eaCoerced
    Nothing -> do
      withBox <- coerce ea tyA' tyA
      case (withBox, eaTh) of
        (Just eaCoerced, Logic)                   -> return $ ABox eaCoerced th'
        (Just eaCoerced, Program) | isVal         -> return $ ABox eaCoerced th'
        (Just eaCoerced, Program) | th'==Program  -> return $ ABox eaCoerced th'
        (Just _,_)   -> err [DD a, DS "should check at L but checks at P"]
        (Nothing,_) -> err [DD a, DS "should have type", DD tyA,
                            DS "or", DD (AAt tyA th'), 
                            DS "but has type", DD tyA',
                            DS "Unable to prove", DD (ATyEq tyA' tyA)]

-- the T_Box* rules
ta a (AAt tyA th') = do
  ea <- ta a tyA
  eaTh <- aGetTh ea
  isVal <- isValue a
  case eaTh of
    Logic                   -> return $ ABox ea th'
    Program | isVal          -> return $ ABox ea th'
    Program | th'==Program   -> return $ ABox  ea th'
    _  -> err [DD a, DS "should check at L but checks at P"]

-- rule T_join
ta (Join s1 s2 strategy) (ATyEq a b) = do
  -- The input (ATyEq a b) is already checked to be well-kinded, 
  -- so we don't need a kind-check here.

  -- Although we aren't changing the context, the operational semantics
  -- will not work well with uninstantiated evars, so we insert a solve here...
  -- (TODO: maybe refine this to only solve for vars that actually occur in a or b?)
  solveConstraints =<< getAvailableEqs
  za <- zonkTerm a
  zb <- zonkTerm b

  t1E <- erase za
  t2E <- erase zb
  -- Test the astep code
  --testReduction =<< substDefs a
  --testReduction =<< substDefs b
  -- End astep test
  joinable <- join s1 s2 t1E t2E strategy
  unless joinable $
    err [DS "The erasures of terms", DD za, DS "and", DD zb,
         DS "are not joinable."]
  return (AJoin a s1 b s2 strategy)

    -- rule T_ord
ta (OrdAx a) (ASmaller b1 b2) = do
     (ea,tyA) <- ts a
     eaTh <- aGetTh ea
     unless (eaTh==Logic) $
       err [DS "The ordering proof", DD a, DS "should check at L but checks at P"]
     zb1 <- zonkTerm b1
     zb2 <- zonkTerm b2
     case eraseToHead tyA of
       ATyEq a1 cvs ->
         case cvs of
           (ADCon _ _ _ vs) -> do
             a1_eq_b2 <- a1 `aeqSimple` zb2
             unless (a1_eq_b2) $
               err [DS "The left side of the equality supplied to ord ",
                    DS "should be", DD zb2, 
                    DS "Here it is", DD a1]
             anySubterm <- anyM (\ (ai,_) -> ai `aeqSimple` zb1) vs
             unless anySubterm $
                err [DS "The right side of the equality supplied to ord ",
                     DS "should be a constructor application involving", DD zb1,
                     DS "Here the equality is", DD tyA,
                     DS "Which has the right hand side", DD cvs]
             return (AOrdAx ea zb1)
           _ -> err [DS "The right side of the equality supplied to ord ",
                     DS "must be a constructor application.",
                     DS "Here it is", DD cvs]
       _ -> err [DS "The argument to ord must be an equality proof.",
                 DS "Here its type is", DD tyA]


-- rule T_contra
ta (Contra a) b =  do 
  -- Note, b is assumed to be already kind-checked.
   (ea, tyA) <- ts a
   eaTh <- aGetTh ea
   case (eaTh, eraseToHead tyA) of
     (Logic, ATyEq cvs1 cvs2) ->
       case (cvs1, cvs2) of
         ((ADCon c1 _ _ vs1), (ADCon c2 _ _ vs2)) ->
            do when (c1 == c2) $
                 err [DS "The equality proof", DD tyA,
                      DS "isn't necessarily contradictory because the",
                      DS "constructors on both sides are the same."]
               vs1Values <- (allM (fmap isEValue . erase . fst) vs1)
               vs2Values <- (allM (fmap isEValue . erase . fst) vs2)              
               unless (vs1Values && vs2Values) $   
                 err [DS "The equality proof", DD tyA,
                      DS "isn't necessarily contradictory because the",
                      DS "constructors are applied to non-values."]
               zb <- zonkTerm b
               return (AContra ea zb)
         _ -> err [DS "The equality proof supplied to contra must show",
                   DS "two different constructor forms are equal.",
                   DS "Here it shows", DD tyA]
     (Logic,_) -> err [DS "The argument to contra must be an equality proof.",
                      DS "Here its type is", DD tyA]
     (Program,_) -> err [DS "The proof argument to contra must check at L, but", DD a,
                       DS "checks at P"]

-- rule T_abort
ta Abort tyA = 
  --Note that tyA is assumed to already be kind-checked.
  return (AAbort tyA)

-- Rules T_lam1 and T_lam2
ta (Lam lep lbody) ty = do
  hyps <- getAvailableEqs
  underHypotheses hyps $ outofArrow ty
    (\arr@(AArrow _ ex aep abody) -> do
      -- Note that the arrow type is assumed to be kind-checked already.

      -- Can't use unbind2 because lbody and abody bind names from 
      -- different languages.
      ((dumb_x,unembed -> tyA),dumb_tyB) <- unbind abody
      (x, body) <- unbind lbody
      let tyB = subst dumb_x (AVar (translate x)) dumb_tyB

      when (lep /= aep) $
           err ([DS "Lambda annotation", DD lep,
                 DS "does not match arrow annotation", DD aep])

      -- typecheck the function body and get its theta
      (ebody, th) <- extendCtxSolve (ASig (translate x) Program tyA) $ do
                 ebody <- ta body tyB
                 (th,_) <- getType ebody
                 return (ebody, th)

      -- perform the FV and value checks if in T_Lam2
      -- The free variables function fv is ad-hoc polymorphic in its
      -- return type, so we fix the type of xE.
      -- If we did (x `S.member` fv bodyE), fv would always return an empty set...
      let xE = translate x :: EName
      bodyE <- erase ebody
      when (lep == Erased && xE `S.member` fv bodyE) $
           err [DS "ta: In implicit lambda, variable", DD x,
                DS "appears free in body", DD body]
      zarr <- zonkTerm arr
      return (ALam th zarr lep (bind (translate x) ebody)))

    (err [DS "Functions should be ascribed arrow types, but",
          DD (Lam lep lbody), DS "was ascribed type", DD ty])

-- rules T_ind1 and T_ind2
-- TODO: to match the ICFP paper we should have an injRng check here too.
ta (Ind ep lbnd) ty = do
  hyps <- getAvailableEqs
  underHypotheses hyps $ outofArrow ty
    (\arr@(AArrow k ex aep abnd) -> do
       -- Note that the the arrow type is assumed to by kind-checked already.

       unless (ep == aep) $
          err [DS "ta : expecting argument of ind to be", DD aep,
               DS "got", DD ep]

       ((old_f, old_y), a) <- unbind lbnd
       let f = translate old_f
       let y = translate old_y
       ((dumb_y, unembed -> tyA), dumb_tyB) <- unbind abnd
       let tyB = subst dumb_y (AVar y) dumb_tyB

       -- next we must construct the type C.  we need new variables for x and z
       x <- fresh (string2Name "x")
       z <- fresh (string2Name "z")
       let xTyB = subst y (AVar x) tyB
           smallerType = ASmaller (AVar x)
                                  (AVar y)

           tyC = AArrow k ex ep (bind (x, embed tyA) 
                              (AArrow k Explicit Erased (bind (z, embed smallerType) xTyB)))
       -- Finally we can typecheck the fuction body in an extended environment
       (ea,eaTh) <- extendCtx (ASig (translate f) Logic tyC) $
                      extendCtxSolve (ASig y Logic tyA) $ do
                        ea <- ta a tyB
                        eaTh <- aGetTh ea
                        return (ea, eaTh)
       unless (eaTh == Logic) $
          err [DS "body of ind must check at L, but here checks at P"]

       -- in the case where ep is Erased, we have the two extra checks:
       aE <- erase ea
       when (ep == Erased && translate y `S.member` fv aE) $
            err [DS "ta: In implicit ind, variable", DD y,
                 DS "appears free in body", DD a]

       when (ep == Erased) $ do
            unless (isEValue aE) $
                   err [DS "The body of an implicit ind must be a value",
                        DS "but here is:", DD a]
       zarr <- zonkTerm arr
       return (AInd zarr ep (bind (f,y) ea)))
    (err [DS "Functions should be ascribed arrow types, but",
          DD (Ind ep lbnd), DS "was ascribed type", DD ty])

-- rules T_rec1 and T_rec2
-- TODO: to match the ICFP paper we should have an injRng check here too.
ta (Rec ep lbnd) ty = do
  hyps <- getAvailableEqs
  underHypotheses hyps $ outofArrow ty
    (\arr@(AArrow k ex aep abnd) -> do
       -- Note that the arrow type is assumed to be already type checked.

       unless (ep == aep) $
              err [DS "ta : expecting argument of rec to be",
                   DD aep, DS ", got", DD ep]

       ((old_f, old_y), a) <- unbind lbnd
       let f = translate old_f
       let y = translate old_y
       ((dumb_y, unembed -> tyA), dumb_tyB) <- unbind abnd
       let tyB = subst dumb_y (AVar y) dumb_tyB

       ea <- extendCtx (ASig f Program arr) $
               extendCtxSolve (ASig y Program tyA) $
                 ta a tyB

       -- perform the FV and value checks if in T_RecImp
       aE <- erase ea
       when (ep == Erased && translate y `S.member` fv aE) $
            err [DS "ta: In implicit rec, variable", DD y,
                 DS "appears free in body", DD a]
       when (ep == Erased) $ do
         unless (isEValue aE) $
            err [DS "ta : The body of an implicit rec must be a value",
                 DS "but here is:", DD a]
       zarr <- zonkTerm arr
       return (ARec zarr ep (bind (f,y) ea)))
    (err [DS "Functions should be ascribed arrow types, but",
          DD (Rec ep lbnd), DS "was ascribed type", DD ty])


    -- Elaborating 'unfold' directives; checking version
ta (Unfold n a b) tyB = do
   (ea,_)  <- ts a
   --ea' <- asteps n ea 
   availableEqs <- getAvailableEqs
   (ea', p) <- smartSteps availableEqs ea n
   x   <- fresh $ string2Name "unfolds"
   y   <- fresh $ string2Name "_"
   (th, eb)  <- extendCtxSolve (ASig x Logic (ATyEq ea ea')) $ do
                  eb <- ta b tyB      
                  th <- aGetTh eb
                  return (th,eb)
   return (ALet Runtime (bind (x, y, embed p) eb) (th, tyB))

   
ta (TerminationCase s binding) ty = err [DS "termination-case is currently unimplemented"]

ta (DCon c args) (ATCon tname eparams) = do
  -- could overload data constructors here
  (_, delta, AConstructorDef _ deltai) <- lookupDCon (translate c)
  unless (length args == aTeleLength deltai) $
           err [DS "Constructor", DD c,
                DS $ "should have " ++ show (aTeleLength deltai)
                 ++ " data arguments, but was given " 
                 ++ show (length args) ++ " arguments."]
  teleRes <- taTele args 
             (substATele delta eparams deltai)
  let (eargs,eths) = unzip teleRes
  return $ (ADCon (translate c) (maximum (minBound:eths)) 
            eparams eargs) 

ta TrustMe ty = return (ATrustMe ty)

-- For InferMes with equality type, we try to create a proof.
-- Other InferMes create unification variables. 
-- We use congruence closure to only require its type to be equivalent 
-- to an equality, rather than being on the nose. 
ta InferMe ty = do
  hyps <- getAvailableEqs
  underHypotheses hyps $ outofTyEq ty
    (\(ATyEq ty1 ty2) -> do
      --It's an equation, prove it.
      pf <- prove hyps (ty1,ty2)   --TODO: don't calculate this CC twice.
      case pf of
        Nothing -> do
          gamma <- getLocalCtx
          err [DS "I was unable to prove:", DD (Goal hyps (ATyEq ty1 ty2))
    --           ,DS "The full local context is", DD gamma
               ]
        Just p -> do
           pE <- erase p
           if (S.null (fv pE :: Set EName))
             then zonkTerm p
             else zonkTerm =<< (uneraseEq ty1 ty2 p))
    (do
       -- It's not an equation, just leave it as a unificatoin variable.
       x <- fresh (string2Name "")
       addConstraint (ShouldHaveType x ty)
       return (AUniVar x ty))

-- rule T_chk
ta a tyB = do
  (ea,tyA) <- ts a 
  noCoercions <- getFlag NoCoercions
  ztyB <- zonkTerm tyB
  tyA_eq_ztyB <- tyA `aeqSimple` ztyB
  if (tyA_eq_ztyB)
    then return ea   --already got the right type.
    else 
     -- try to use a cumul
     case maybeCumul ea tyA ztyB of
       Just eaCumuled -> return eaCumuled
       Nothing ->
        -- try to insert an equality proof.
        if (not noCoercions)
         then do
           context <- getTys
           availableEqs <- getAvailableEqs
           let theGoal = (Goal availableEqs (ATyEq tyA ztyB))
           pf <- prove availableEqs (tyA,ztyB)
           case pf of 
             Nothing ->
               err [DS "When checking term", DD a, DS "against type",
                    DD tyB,  -- DS ("(" ++ show tyB ++ ")"),
                    DS "the distinct type", DD tyA, -- DS ("(" ++ show tyA ++"("),
                    DS "was inferred instead.",
                    DS "I was unable to prove:", DD theGoal]
             Just p -> do
                    -- If the two types contained unification variables they may be identical now,
                    -- in which case we do not need to insert a conversion after all.
                    zztyA <- zonkTerm tyA
                    zztyB <- zonkTerm ztyB
                    if (zztyA `aeq` zztyB)
                      then zonkTerm ea
                      else do
                         zonkTerm $ AConv ea p
         else err [DS "When checking term", DD a, DS "against type",
                   DD ztyB,  DS ("(" ++ show ztyB ++ ")"),
                   DS "the distinct type", DD tyA, DS ("("++ show tyA++")"),
                   DS "was inferred instead.",
                   DS "(No automatic coersion was attempted.)"]

-- maybeCumul a tyA tyB 
-- tries to insert a use of ACulum to change tyA to tyB.
maybeCumul :: ATerm -> ATerm -> ATerm -> Maybe ATerm
maybeCumul a (eraseToHead -> AType l1) (eraseToHead -> AType l2) =
  if (l1 == l2)
    then Just a 
    else if (l1 < l2)
      then Just (ACumul a l2)
      else Nothing
maybeCumul _ _ _ = Nothing

-- coerce a tyA tyB
-- Tries to use equational reasoning to change the type of a from tyA to tyB.
coerce :: ATerm -> ATerm -> ATerm -> TcMonad (Maybe ATerm)
coerce a tyA tyB = do
  noCoercions <- getFlag NoCoercions
  tyA_eq_tyB <- tyA `aeqSimple` tyB
  if (tyA_eq_tyB)
    then return (Just a)   --already got the right type.
    else 
     -- try to use a cumul
     case maybeCumul a tyA tyB of
       Just aCumuled -> return (Just aCumuled)
       Nothing ->
        -- try to insert an equality proof.
        if noCoercions
         then return Nothing
         else do
           context <- getTys
           availableEqs <- getAvailableEqs
           pf <- prove availableEqs (tyA,tyB)
           case pf of 
             Nothing -> return Nothing
             Just p -> do
                    -- If the two types contained unification variables they may be identical now,
                    -- in which case we do not need to insert a conversion after all.
                    ztyA <- zonkTerm tyA
                    ztyB <- zonkTerm tyB
                    if (ztyA `aeq` ztyB)
                      then Just <$> zonkTerm a
                      else do
                         Just <$> (zonkTerm $ AConv a p)

-- | Checks a list of terms against a telescope of types
-- with the proviso that each term needs to check at Logic.
-- Returns list of elaborated terms.
-- Precondition: the two lists have the same length.
--
-- Unlike ta, here the telescope is not assumed to already be zonked.
taLogicalTele ::  [(Term,Epsilon)] -> ATelescope -> TcMonad [(ATerm,Epsilon)]
taLogicalTele [] AEmpty = return []
taLogicalTele ((t,ep1):terms) (ACons (unrebind->((x,unembed->ty,ep2),tele')))  = do
  unless (ep1 == ep2) $
    err [DS "The term ", DD t, DS "is", DD ep1, DS "but should be", DD ep2]
  zty <- zonkTerm ty
  et <- ta t zty
  etTh <- aGetTh et
  unless (etTh == Logic) $
    err [DS "Each argument needs to check logically, but", 
         DD t, DS "checks at P"]
  eterms <- taLogicalTele terms (simplSubst x et tele')
  zet <- zonkTerm et
  return $ (zet,ep1) : eterms
taLogicalTele _ _ = error "Internal error: taTele called with unequal-length arguments"    


-- | Checks a list of terms against a telescope of types,
-- Returns list of elaborated terms
-- Precondition: the two lists have the same length.
--
-- Unlike ta, here the telescope is not assumed to already be zonked.
taTele ::  [(Term,Epsilon)] -> ATelescope -> TcMonad [((ATerm,Epsilon),Theta)]
taTele [] AEmpty = return []
taTele ((t,ep1):terms) (ACons (unrebind->((x,unembed->ty,ep2),tele')))  = do
  unless (ep1 == ep2) $
    err [DS "The term ", DD t, DS "is", DD ep1, DS "but should be", DD ep2]
  zty <- zonkTerm ty
  et <- ta  t zty
  etTh <- aGetTh et
  --Fixme: need to check that erased arguments are logical.
  eterms <- taTele terms (simplSubst x et tele')
  zet <- zonkTerm et
  return $ ((zet,ep1),etTh) : eterms
taTele _ _ = error "Internal error: taTele called with unequal-length arguments"    

-- Expressions which are always synthesized, so we don't gain anything
-- from checking them against a given type. (partial list, this is a bit of a hack).
unCheckable :: Term-> Bool
unCheckable (Var _) = True
unCheckable (App _ _ _) = True
unCheckable (Ann _ _) = True
unCheckable (Paren t) = unCheckable t
unCheckable (Pos _ t) = unCheckable t
unCheckable _ = False

------------------------------
------------------------------
-------- Synthesis
------------------------------
------------------------------

-- | type synthesis
-- Returns (elaborated term, type of term)
ts :: Term -> TcMonad (ATerm,ATerm)
ts (Pos p t) =
  extendSourceLocation (Just p) t $       
    ts t

ts (Paren a) = ts a

-- Rule T_var/T_unboxVal/T_fo
{- Variables are special, because both the intro and elimination
   rules for @ always apply, so without loss of generality we can
   eagerly apply unbox to the type we looked up from the
   context. While we are at it, we apply as well.       

   Note/todo/wontfix: currently T_unboxVal and T_fo are only ever
   applied to variables in the surface language, not other kinds
   of values, even though that is also allowed in the core
   language.
 -}
ts (Var y) = do
     (th,ty) <- lookupTy (translate y)
     zty <- zonkTerm ty
     (_, adjust_y, adjust_ty) <- adjustTheta th (AVar (translate y)) zty
     return (adjust_y, adjust_ty)

ts (Explicitize a) = do
  do (th,ty) <- ts a
     hasInf <- hasInferreds ty
     unless hasInf $
       err [ DS "Requested to make explicitize", DD a,
             DS "but there are no inferred arguments in its type", DD ty]
     (th,) <$> explicitizeInferreds ty

-- Rule T_type
ts (Type l) = return (AType l,  AType (l + 1))


-- Rule T_pi
ts (Arrow ex ep body) =
  do ((x,unembed -> tyA), tyB) <- unbind body
     etyA <- kcElabFirstOrder tyA
     (etyATh, tytyA) <- getType etyA
     (etyB, etyBTh, tytyB) <- 
       -- this was Program instead of etyATh, why?
       extendCtxSolve (ASig (translate x) etyATh etyA) $ do 
         (etyB, tytyB) <- ts tyB
         etyBTh <- aGetTh etyB
         return (etyB, etyBTh, tytyB)
     unless (etyATh == Logic) $
        err [DS "domain of an arrow type must check logically, but", DD tyA, DS "checks at P"]
     unless (etyBTh == Logic) $
        err [DS "co-domain of an arrow type must check logically, but", DD tyB, DS "checks at P"]
     case (eraseToHead tytyA, eraseToHead tytyB) of
       (AType n, AType m) -> return $ (AArrow (max n m) ex ep  (bind (translate x,embed etyA) etyB), AType (max n m))
       (AType _, _)       -> err [DD tyB, DS "is not a type."]
       (_,_)              -> err [DD tyA, DS "is not a type.", 
                                  DS "It has type", DD tytyA]

-- Rules T_tcon and T_acon 
ts (TCon c args) =
  do (delta, lev, _) <- lookupTCon (translate c)
     unless (length args == aTeleLength delta) $
       err [DS "Datatype constructor", DD c, 
            DS $ "should have " ++ show (aTeleLength delta) ++
                " parameters, but was given", DD (length args)]
     eargs <- taLogicalTele args delta
     return (ATCon (translate c) (map fst eargs), (AType lev))

-- Rule D | _dcon
-- In the synthesizing version, we try to use unification to figure out the type parameters.
ts (DCon c args) = do
     (tname, delta, AConstructorDef _ deltai) <- lookupDCon (translate c)
     (us,deltai') <- instantiateInferredsTele delta deltai
     teleRes <- taTele args deltai'
     let (eargs,eths) = unzip teleRes
     zus <- zonk us
     aKc (ATCon tname zus)
     return $ (ADCon (translate c) (maximum (minBound:eths)) 
               zus eargs, ATCon tname zus )

-- rule T_app
ts tm@(App ep a b) =
  do hyps <- getAvailableEqs
     -- We want to use the same congruence closure to coerce the applied term to a function type
     --   (intoArrow) and to check the injectivity condition (injRng). Computing it twice would be
     --   wasteful, so instead we lift most of this function to run inside the State monad.
     underHypotheses hyps $ do 
       (eaPrecoerce, tyPrecoerce) <- lift $ ts a
       coerced <- intoArrow eaPrecoerce tyPrecoerce
       case coerced of
         Nothing ->  err [DS "ts: expected arrow type, for term ", DD a,
                          DS ". Instead, got", DD tyPrecoerce]
         Just (eaPreinst, tyPreinst) -> do
           (ea,tyArr) <- lift $ instantiateInferreds eaPreinst tyPreinst        
           case eraseToHead tyArr of
             AArrow _ ex epArr bnd -> do
               ((x,tyA),tyB) <- unbind bnd
               unless (ep == epArr) $
                 err [DS "Application annotation", DD ep, DS "in", DD tm,
                      DS "doesn't match arrow annotation", DD epArr]

               -- check the argument, at the "A" type
               eb <- lift $ ta b (unembed tyA)

               -- Erased arguments must terminate
               when (ep==Erased) $ do
                 ebTh <- lift $ aGetTh eb
                 unless (ebTh==Logic) $
                   err [DS "Erased arguments must terminate, but", DD b, DS "checks at P."]

               zea <- lift $ zonkTerm ea
               ztyB <- lift $ zonkTerm tyB

               -- check that the injRng condition holds
               injRngFor tyArr eb

               -- check that the result kind is well-formed
               let b_for_x_in_B = simplSubst x eb ztyB
               lift $ aKc b_for_x_in_B

               return (AApp ep zea eb b_for_x_in_B, b_for_x_in_B)
             _ -> error "internal error. intoArrow somehow produced a non-arrow type"

-- rule T_smaller
ts (Smaller a b) = do
  (ea,_) <- ts a
  (eb,_) <- ts b
  zea <- zonkTerm ea
  return $ (ASmaller zea eb, AType 0)

-- rule T_ordtrans
ts (OrdTrans a b) = do
  (ea,tyA) <- ts a
  eaTh <- aGetTh ea
  unless (eaTh == Logic) $
    err [DS "The ordering proof", DD a, DS "should check at L but checks at P"]
  (eb,tyB) <- ts b
  ebTh <- aGetTh eb
  unless (ebTh== Logic) $
    err [DS "The ordering proof", DD b, DS "should check at L but checks at P"]
  zea <- zonkTerm ea
  ztyA <- zonkTerm tyA
  case (eraseToHead ztyA, eraseToHead tyB) of 
    (ASmaller a1 a2, ASmaller b1 b2) -> do
      a2_eq_b1 <- a2 `aeqSimple` b1
      unless (a2_eq_b1) $
        err [DS "The middle terms of the inequalities given to ordtrans must match, ",
             DS "but here they are", DD a2, DS "and", DD b1]
      return $ (AOrdTrans zea eb, ASmaller a1 b2)
    _ -> err [DS "The arguments to ordtrans must be proofs of <, ",
              DS "here they have types", DD tyA, DS "and", DD tyB]

-- rule T_eq
ts (TyEq a b) = do
  (ea,_) <- ts a 
  (eb,_) <- ts b 
  zea <- zonkTerm ea
  return $ (ATyEq zea eb, AType 0)

-- Datatype injectivity. This is rough-and-ready, since it will be merged into the 
-- congruence closure implementation rather than being exposed in the surface language.
ts (InjDCon a i) =
  do (ea,_) <- ts a
     (_, ty) <- getType (AInjDCon ea i)
     return (AInjDCon ea i, ty)

-- rule T_annot
ts (Ann a tyA) =
  do etyA <- kcElab tyA
     ea <- ta a etyA
     zetyA <- zonkTerm etyA
     return (ea, zetyA)
-- the synthesis version of rules T_let1 and T_let2
-- TODO, maybe these are dubious from the point-of-view of programming-up-to-CC, so we should get rid of them?
ts (Let th' ep bnd) =
 do -- begin by checking syntactic -/L requirement and unpacking binding
    when (ep == Erased && th' == Program) $
      err [DS "Implicit lets must bind logical terms."]
    ((x,y,unembed->a),b) <- unbind bnd
    -- premise 1
    (ea,tyA) <- ts a
    aTh <- aGetTh ea
    unless (aTh <= th') $
      err [DS "The variable", DD y, DS "was marked as L but checks at P"]
    -- premise 2
    (eb,tyB, bTh) <- extendCtx (ASig (translate y) Logic (ATyEq (AVar (translate x)) ea)) $
                     extendCtxSolve (ASig (translate x) th' tyA) $ do
                        (eb, tyB) <- ts b
                        bTh <- aGetTh eb
                        return (eb, tyB, bTh)
    -- premise 3
    aKc tyB

    -- premises 4 and 5
    bE <- erase eb
    when (translate y `S.member` fv bE) $
      err [DS "The equality variable bound in a let is not allowed to",
           DS "appear in the erasure of the body, but here", DD y,
           DS "appears in the erasure of", DD b]
    when (ep == Erased && translate x `S.member` fv bE) $
      err [DS "The variables bound in an implicit let are not allowed to",
           DS "appear in the erasure of the body, but here", DD x,
           DS "appears in the erasure of", DD b]

    zea <- zonkTerm ea
    return (ALet ep (bind (translate x, translate y,embed zea) eb) 
            (max th' bTh,tyB), tyB)

-- T_at
ts (At tyA th') = do
  (ea,s) <- ts tyA
  eaTh <- aGetTh ea
  case (eaTh,eraseToHead s) of
    (Logic, AType i) -> return (AAt ea th',s)
    (Program,AType i) -> err [DS "Types should check at L, but", DD tyA, DS "checks at P"]
    (_,_)             -> err [DS "Argument to @ should be a type, here it is", DD tyA, DS "which has type", DD s]

ts tm = err $ [DS "Sorry, I can't infer a type for:", DD tm,
                DS "Please add an annotation.",
                DS "NB: This error happens when you misspell,",
                DS "so check your spelling if you think you did annotate."]

-- | Take an annotated term which typechecks at aTy, and try to
--   apply as many Unboxing rules as possible.
adjustTheta :: Theta -> ATerm -> ATerm -> TcMonad (Theta, ATerm, ATerm)
adjustTheta th a aTy = do
  isVal <- isEValue <$> erase a
  case eraseToHead aTy of
   (AAt ty' th') ->
       case (isVal, th) of
         (True, _)        -> adjustTheta th' (AUnbox a) ty'
         (False, Logic)   -> adjustTheta th' (AUnbox a) ty'
         (False, Program) -> adjustTheta Program (AUnbox a) ty'
   _  -> return (th, a, aTy)

-- | Take a term which perhaps has an inferred arrow type (that is, (x1:A1)=>...(xn:An)=>B), 
-- and replace the xs with unification variables.
instantiateInferreds :: ATerm -> ATerm -> TcMonad (ATerm,ATerm)
instantiateInferreds a (eraseToHead -> AArrow _ Inferred ep bnd) = do
  ((x,unembed->aTy),bTy) <- unbind bnd
  n <- fresh (string2Name "")
  addConstraint (ShouldHaveType n aTy)
  let bTy' = subst x (AUniVar n aTy) bTy
  instantiateInferreds (AApp ep a (AUniVar n aTy) bTy') bTy'
instantiateInferreds a aTy = return (a, aTy)

-- | Create new unification variables for each variable in the telescope,
--  and replace all occurances of those variables in a.
instantiateInferredsTele :: Subst ATerm a => ATelescope -> a -> TcMonad ([ATerm],a)
instantiateInferredsTele AEmpty a = return ([],a)
instantiateInferredsTele (ACons (unrebind->((x,unembed->ty,ep),tele))) a = do
  n <- fresh (string2Name (name2String x ++ "_inf"))
  addConstraint (ShouldHaveType n ty)
  let u = (AUniVar n ty)
  (us, a') <-  instantiateInferredsTele tele (subst x u a)
  return (u:us, a')
   

-- | Is 'a' an arrow type that has inferred arguments?
hasInferreds :: ATerm -> TcMonad Bool
hasInferreds (eraseToHead -> AArrow _ Inferred ep bnd) = return True
hasInferreds (eraseToHead -> AArrow _ Explicit ep bnd) = do
  ((x,_),bTy) <- unbind bnd
  hasInferreds bTy
hasInferreds _ = return False

-- | Make all the inferred arguments of an arrow type explicit.
explicitizeInferreds :: ATerm -> TcMonad ATerm 
explicitizeInferreds (eraseToHead -> AArrow th _ ep bnd) = do
  ((x,aTy),bTy) <- unbind bnd
  bTy' <- explicitizeInferreds bTy
  return $ AArrow th Explicit ep (bind (x,aTy) bTy')
explicitizeInferreds a = return a 

--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each modules
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked and elaborated into the core
-- language.
tcModules :: [Either Module AModule] -> TcMonad [AModule]
tcModules mods = foldM tcM [] mods
  -- Check module m against modules in defs, then add m to the list.
  where defs `tcM` (Left m) = do -- "M" is for "Module" not "monad"
          liftIO $ putStrLn $ "Checking module " ++ show (moduleName m)
          m' <- defs `tcModule` m
          return $ defs++[m']
        defs `tcM` (Right am) = do
          liftIO $ putStrLn $ "Using the pre-compiled module " ++ show (aModuleName am)
          return $ defs ++ [am]

-- | Typecheck an entire module.
tcModule :: [AModule]        -- ^ List of already checked modules (including their Decls).
         -> Module           -- ^ Module to check.
         -> TcMonad AModule  -- ^ The same module with all Decls checked and elaborated.
tcModule defs m' = do 
  -- Doing this filter is not good because it makes the language fail "regularity", 
  --  i.e. one of the imported types may not be well-formed (because it assumed a bigger context)
  --let importedModules = filter (\x -> (ModuleImport (aModuleName x)) `elem` moduleImports m') defs
  let importedModules = defs
  checkedEntries <- extendCtxMods importedModules $ 
                      do
                        cutoff <- length <$> getCtx
                        (drop cutoff . reverse) <$> tcEntries (moduleEntries m')
  return $ AModule (moduleName m') checkedEntries (moduleConstructors m')

tcEntries :: [Decl] -> TcMonad [ADecl]
tcEntries (Def n term : decls) = do
  oldDef <- lookupDef (translate n)
  case oldDef of
    Nothing -> tc
    Just term' -> die term'
  where
    tc = do
      lkup <- lookupHint (translate n)
      case lkup of
        Nothing -> do 
          (eterm,ty) <- ts term
          th <- aGetTh eterm
          -- Put the elaborated version of term 
          -- into the context.
          extendCtxsGlobal [ADef (translate n) eterm,
                            ASig (translate n) th ty] $
            tcEntries decls
        Just (theta,ty) -> do
            eterm <- ta term ty 
            etermTh <- aGetTh eterm
            unless (etermTh <= theta) $
              err [DS "The variable", DD n, 
                   DS "was marked as L but checks at P"]
            -- If we already have a type in the environment, due to a sig
            -- declaration, then we don't add a new signature.
            --
            -- Put the elaborated version of term into the context.
            extendCtxsGlobal [ADef (translate n) eterm,
                              ASig (translate n) theta ty] $
              tcEntries decls
    die term' =
      extendSourceLocation (unPosDeep term) term $
         err [DS "Multiple definitions of", DD n,
              DS "Previous definition was", DD term']

tcEntries (Sig n th ty : decls) = do
  duplicateTypeBindingCheck n ty
  ety <- kcElab ty
  tyTh <- aGetTh ety
  unless (tyTh <= th) $
    err [DS "The variable", DD n, DS "was marked as L, but", DD ty, DS "checks at P"]
  extendHints (AHint (translate n) th ety) $
    tcEntries decls

tcEntries (Axiom n th ty : decls) = do
  duplicateTypeBindingCheck n ty
  ety <- kcElab ty
  tyTh <- aGetTh ety
  unless (tyTh <= th) $
    err [DS "The variable", DD n, DS "was marked as L, but", DD ty, DS "checks at P"]
  extendCtxsGlobal [ADef (translate n) (ATrustMe ety),
                    ASig (translate n) th ety] $
    tcEntries decls

-- rule Decl_data
tcEntries (Data t delta lev cs : decls) =
  do -- The parameters of a datatype must all be Runtime.
     unless (all (\(_,_,ep) -> ep==Runtime) delta) $
       err [DS "All parameters to a datatype must be marked as relevant."]
     ---- Premise 1
     edelta <- kcTele delta
     ---- Premise 2: check that the telescope provided 
     ---  for each data constructor is wellfomed, and elaborate them
     ---  fixme: probably need to worry about universe levels also?
     let elabConstructorDef defn@(ConstructorDef pos d tele) =
            extendSourceLocation (Just pos) defn $ 
              extendCtx (AAbsData (translate t) edelta lev) $
                extendCtxTele edelta Program $ do
                  etele <- kcTele tele
                  return (AConstructorDef (translate d) etele)
     ecs <- mapM elabConstructorDef cs
     -- Premise 3: check that types are strictly positive.
     mapM_ (positivityCheck t) cs
     -- Implicitly, we expect the constructors to actually be different...
     let cnames = map (\(ConstructorDef _ c _) -> c) cs
     unless (length cnames == length (nub cnames)) $
       err [DS "Datatype definition", DD t, DS"contains duplicated constructors" ]
     -- finally, add the datatype to the env and perform action m
     extendCtxsGlobal [AData (translate t) edelta lev ecs] $
       tcEntries decls

tcEntries (AbsData t delta lev : decls) = do
  edelta <- kcTele delta
  extendCtxsGlobal [AAbsData (translate t) edelta lev] $
    tcEntries decls

tcEntries (UsuallyTheta dth : decls) = 
  withDefaultTheta dth $ tcEntries decls

tcEntries [] = getCtx

duplicateTypeBindingCheck :: TName -> Term -> TcMonad ()
duplicateTypeBindingCheck n ty = do
  -- Look for existing type bindings ...
  l  <- lookupTyMaybe (translate n)
  l' <- lookupHint (translate n)
  -- ... we don't care which, if either are Just.
  case catMaybes [l,l'] of
    [] ->  return ()
    -- We already have a type in the environment so fail.
    (_,ty'):_ ->
      let (Pos p  _) = ty
          msg = [DS "Duplicate type signature ", DD ty,
                 DS "for name ", DD n,
                 DS "Previous typing was", DD ty']
       in
         extendSourceLocation (Just p) ty $ err msg
    
-- Positivity Check

-- | Determine if a data type only occurs in strictly positive 
-- positions in a constructor's arguments.

positivityCheck
  :: (Fresh m, MonadError Err m, MonadReader Env m) =>
     Name Term -> ConstructorDef -> m ()
positivityCheck tName (ConstructorDef _ cName tele)  = do
  mapM_ checkBinding tele
   `catchError` rethrowWith msg'
  where checkBinding (_,teleTy,_) = occursPositive tName teleTy
        msg' = text "When checking the constructor" <+> disp cName

occursPositive  :: (Fresh m, MonadError Err m, MonadReader Env m) => 
                   Name Term -> Term -> m ()
occursPositive tName (Pos p ty) = do
  extendSourceLocation (Just p) ty $
    occursPositive tName ty 
occursPositive tName (Paren ty) = occursPositive tName ty
occursPositive tName (Arrow _ _ bnd) = do
 ((_,unembed->tyA), tyB) <- unbind bnd
 when (tName `S.member` (fv tyA)) $
    err [DD tName, DS "occurs in non-positive position"]
 occursPositive tName tyB
occursPositive tName ty = do
  let children = subtrees ty
  mapM_ (occursPositive tName) children


-- Alpha equality up to erasure

aeqSimple :: ATerm -> ATerm -> TcMonad Bool
aeqSimple a b = do
  aE <- erase a
  bE <- erase b
  return $ aE `aeq` bE

---------------------------------------------------------------------------
-- Looking up datatypes in the context, when typechecking case-expressions.
---------------------------------------------------------------------------

-- | If bty is a datatype, then return its definition, otherwise signal an error.
lookupDType :: Disp a => a -> ATerm -> TcMonad (AName, [ATerm], ATelescope, [AConstructorDef])
lookupDType b bty@(eraseToHead -> ATCon d params) = do
         ent <- lookupTCon d
         case ent of
           (delta,_,Just cons) ->
             do unless (length params == aTeleLength delta) $
                   err [DS "Attempted to match against", DD b,
                        DS "with type", DD bty, DS "where", DD d,
                        DS "is applied to the wrong number of arguments."]
                return (d, params, delta, cons)
           (_,_,Nothing) ->
              err [DS "Scrutinee ", DD b,
                   DS "is a member of an abstract datatype - you may not",
                   DS "pattern match on it."]
lookupDType b bty = err [DS "Scrutinee ", DD b,
                         DS "must be a member of a datatype, but is not. It has type", DD bty]


-------------------------------------------------------
-- Dig through the context, select all "interesting" bindings,
-- apply adjustTheta as appropriate,
-- return a suitable list of assumptions for unification/typeclass inference.

{- Open issues:
   - Which things are "interesting"? For unification, we probably want only equations.
     Currently I include everything, but if that turns out to be too slow
     we might want to have a mechanism to identify types which should be 
     subject to guessing for typeclasses, and only select those.
   - Is the adjustTheta ok? It could be a problem if we actually want to 
     find an inhabitant of a boxed type.
-}
-------------------------------------------------------

-- Note, the returned value is already zonked
getAvailableEqs :: TcMonad [(Theta, ATerm, ATerm)]
                                   --proof --type of proof
getAvailableEqs = do
  context <- getLocalCtx
  catMaybes <$> mapM (\d -> case d of
                              ASig x th ty -> do
                                                 zty <- zonkTerm ty
                                                 -- could return Nothing here, for "uninteresting" things
                                                 Just <$> adjustTheta th (AVar x) zty
                              _    -> return Nothing)
                     context

----------------------------------------------------------
-- Work in an extended context, then try to solve any remaining unification vars.
extendCtxSolve :: (Rep a) => ADecl -> TcMonad a -> TcMonad a
extendCtxSolve d m =
  extendCtx d
            (do 
               isTypeclassy <- getFlag Typeclassy
               res <- m
               when isTypeclassy $
                 solveConstraints =<< getAvailableEqs
               zonk res)

-------------------------------------
-- Elaborating complex pattern matches
--
-- This is mostly the same as the algorithm described in 
--     Philip Wadler, "Efficient Compilation of Pattern-Matching",
--     a chapter in Simon Peyton-Jones, _The Implementation of Functional Programming Languages_.
--
--  Consider each scrutinee in turn from left to right, adding
--  new case statements.
-- 
--  One twist which is different from, e.g., Coq, is that if we have
--    case e of x -> b
--  where e is not a variable, we must add a let statement to the
--  elaborated program. We can not just substitute e for x, because of value restriction. 
--
--  Also, unlike haskell, we want to signal an error for non-exhaustive matches.
-----------------------------------------

{- Problems to be fixed:
    * The treatment of equations for the scrutinees is dubious. 
      The named equation should actually equate the scrutinee with the full nested pattern.
    * Need to think/test the logic for empty case statements a bit more, probably.
 -}

-- (buildCase scrutinees alts tyAlt) builds a case tree that evaluates to the
-- first alternative that matches, or 'fallback' if none of them do.  Each
-- branch in alts should have type tyAlt.
--
-- precondition: all the pattern lists have the same length as scrutinees.
--
-- The scrutinees and the branch-type are zonked before buildCase is called.
--
--            scrutinee  equation-name    branches          branch-type
buildCase :: [(ATerm,    TName)]       -> [ComplexMatch] -> ATerm        -> TcMonad ATerm
buildCase [] [] _ = err [DS "Patterns in case-expression not exhaustive."]
buildCase [] ((ComplexMatch bnd):_) tyAlt = do
  ([], body) <- unbind bnd  --no more patterns to match.
  ta body tyAlt
buildCase ((s,y):scruts) alts tyAlt | not (null alts) && not (isAVar s) && any isEssentialVarMatch alts = (do
  -- If one of the patterns contains an isolated variable, 
  -- the ComplexCase basically acts as
  --  a let-expression, so that's what we elaborate it into.
  -- SCW: Shouldn't it be the *first* alt?
  x <- fresh (string2Name "_scrutinee")
  x_eq <- fresh (string2Name "_")
  (th,sTy) <- getType s 
  ztyAlt <- zonkTerm tyAlt
  (body, bTh) <- extendCtx (ASig x th sTy) $
           extendCtx (ASig x_eq Logic (ATyEq (AVar x) s)) $ do
             body <- buildCase ((AVar x,y):scruts) alts ztyAlt
             bTh  <- aGetTh body
             return (body, bTh)
  return (ALet Runtime (bind (x, x_eq, embed s) body) (max th bTh, ztyAlt)))

buildCase ((s,y):scruts) alts tyAlt | not (null alts) && all isVarMatch alts = (do
  --Todo: handle the scrutinee=pattern equation y somehow?
  alts' <- mapM (expandMatch s AEmpty <=< matchPat) alts
  buildCase scruts alts' tyAlt)

-- normal pattern matching case. First pattern is not a variable.
buildCase ((s_unadjusted,y):scruts) alts tyAlt = (do
  (th_unadjusted, sTy_unadjusted) <- getType s_unadjusted
  (aTh,s,sTy) <- adjustTheta th_unadjusted s_unadjusted sTy_unadjusted
  (d, bbar, delta, cons) <- lookupDType s sTy
  when (null alts && not (null cons)) $
    err $[DS "Patterns in case-expression not exhaustive."]
  let buildMatch :: AConstructorDef -> TcMonad (AMatch, Theta)
      buildMatch (AConstructorDef c args) = do
        relevantAlts <- filter (\(p,_) -> case p of 
                                           (PatCon (unembed -> c') _) -> (translate c')==c
                                           (PatVar _) -> True)
                           <$> mapM matchPat alts
        let nameSuggestions = suggestedNames (map ("_pat_"++) (aTeleNames args)) (map fst relevantAlts)
        args' <- freshATele nameSuggestions args
        newScruts <- mapM (\x -> ((AVar (translate x)), ) <$> (fresh $ string2Name "_")) (binders args' :: [AName])
        let newScrutTys = simplSubsts (zip (binders delta) bbar) args'
        newAlts <- mapM (expandMatch s args') relevantAlts
        let erasedVars = aTeleErasedVars args'
                         `S.union` (S.singleton (translate y))
        ztyAlt <- zonkTerm tyAlt
        let extend = extendCtxTele newScrutTys aTh . 
             extendCtx (ASig (translate y) Logic 
                     (ATyEq s (ADCon c aTh bbar (aTeleAsArgs args'))))
        newBody <- extend $
                       buildCase (newScruts++scruts) newAlts ztyAlt
                                                   
        (th,_) <- extend $ getType newBody
        erasedNewBody <- erase newBody
        unless (S.null (S.map translate (fv erasedNewBody) `S.intersection` erasedVars)) $ do
          let (x:_) = S.toList (fv newBody `S.intersection` erasedVars)
          err [DS "The variable", DD x, DS "is marked erased and should not appear in the erasure of the case expression"]
        znewScrutTys <- zonkTele newScrutTys
        return $ (AMatch c (bind znewScrutTys newBody), th)
  builds <- mapM buildMatch cons
  let (matchs, ths) = unzip builds
  let ematchs = bind (translate y)  matchs
  ztyAlt <- zonkTerm tyAlt
  let th = maximum (aTh : ths) 
  return $ ACase s ematchs (th,ztyAlt))

-- Given a list of Patterns (which should all be for the same datatype),
-- see if there is any commonality in the name of the pattern variables, and if so
-- give back a list of them.
-- If none are given, use the default ones.
-- The list we construct always has the same length as the default list, even if some 
-- patterns (incorrectly) provided more or fewer (in order to give better error messages).
suggestedNames :: [String] -> [Pattern] -> [String]
suggestedNames deflt (PatVar _ : rest) = suggestedNames deflt rest
suggestedNames deflt (PatCon _ args : rest) =
  zipWith (\new old -> case new of 
                           Nothing -> old
                           Just s -> s)
          (map (suggestedName . fst) args ++ repeat Nothing)
          (suggestedNames deflt rest)
suggestedNames deflt [] = deflt

suggestedName :: Pattern -> Maybe String 
suggestedName (PatVar s) = Just (name2String s)
suggestedName _ = Nothing

aTeleNames :: ATelescope -> [String]
aTeleNames AEmpty = []
aTeleNames (ACons (unrebind -> ((x,ty,ep),t))) = (name2String x) : aTeleNames t

-- | expandMatch scrut args (pat, alt) 
-- adjusts the ComplexMatch 'alt'
-- for the fact that 'scrut' has just been sucessfully tested against
-- pattern pat.  It adds the new variables args to the list of
-- patterns for alt, and substitutes scrut into the body of alt if
-- 'pat' was a variable pattern.
-- Precondition: scrut is a variable (so we can substitute it into the body).

expandMatch :: ATerm ->  ATelescope -> (Pattern, ComplexMatch) -> TcMonad ComplexMatch
expandMatch s  args (PatCon (unembed -> c) newPats, ComplexMatch alt) = do
  unless (length newPats == aTeleLength args) $ 
    err [DS "constructor", DD c, DS $ "should take " ++ show (aTeleLength args) ++ " constructors,",
         DS "but the pattern", DD (PatCon (embed c) newPats), DS $ "has " ++ show (length newPats) ++ "."]
  unless (aTeleEpsilons args == map snd newPats) $
    err [DS "wrong epsilons on arguments in pattern", DD (PatCon (embed c) newPats)]
  (pats, body) <- unbind alt
  return $ ComplexMatch (bind (map fst newPats++pats) body)
expandMatch s args (PatVar z, ComplexMatch alt) = do
  newPats <- mapM (\ep -> do x <- fresh (string2Name  "_"); return (PatVar x, ep)) (aTeleEpsilons args)
  (pats, body) <- unbind alt
  case (eraseToHead s) of 
    AVar x ->
      return $ ComplexMatch (bind (map fst newPats++pats) (simplSubst z (Var (translate x)) body))
    _ ->
      if S.member z (fv body)
        then  error "internal error: buildCase failed to let-expand an essential pattern variable"
        else  return $ ComplexMatch (bind (map fst newPats++pats) body)


--Is the first pattern on the list a PatVar?
isVarMatch :: ComplexMatch -> Bool
isVarMatch (ComplexMatch bnd) = 
 --unsafeUnbind is ok since we never look at the names, only the top constructor.
 let (pats, _) = unsafeUnbind bnd in
 case pats of
   (PatVar _ : _) -> True
   _ -> False

--Is the first pattern on the list a PatVar which is free in the body (as opposed to 
-- a wildcard?  (Can have occasional false positives).
isEssentialVarMatch :: ComplexMatch -> Bool
isEssentialVarMatch (ComplexMatch bnd) = 
  -- This use of unsafeUnbind could cause the function to incorrectly return
  -- true. Callers of the functions need to be ok with that.
  let (pats, body) = unsafeUnbind bnd in
  case pats of 
    (PatVar x : _) -> x `S.member` fv body
    _ -> False
 

-- Precondition: the match has at least one pattern.
matchPat :: (Functor m, Fresh m) => ComplexMatch -> m (Pattern, ComplexMatch)
matchPat (ComplexMatch bnd) = do
  ((pat:pats), body) <- unbind bnd
  return (pat, ComplexMatch $ bind pats body)

