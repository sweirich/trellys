{-# LANGUAGE ViewPatterns, TypeSynonymInstances, ExistentialQuantification, NamedFieldPuns, 
             ParallelListComp, FlexibleContexts, ScopedTypeVariables, TupleSections #-}
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

import Language.Trellys.GenericBind
import qualified Language.Trellys.GenericBind as GB
import Generics.RepLib.Lib(subtrees)
import Text.PrettyPrint.HughesPJ

import Control.Applicative ((<$>))
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)

import qualified Generics.RepLib as RL

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

{-
  We rely on two mutually recursive judgements:

  * ta is an analysis judgement that takes a term and a type and checks it.

  * ts is a synthesis that takes a term and synthesizes a type.

  Both functions also return an annotated term which is an
  elaborated version of the input term. The invariants for this is:
   - ta takes a source term and elaborated type, returns elaborated term
     - The elaborated type has already been kind-checked, ta will not re-check it.
   - ts takes a source term, returns elaborated term and elaborated type.
     - The elaborated type is guaranteed to be well-kinded
  
  From the elaborated term, we can also recover the minimal theta that makes 
  that term typecheck. So these two functions also implicitly compute th.

  In both functions, the context (gamma) is an implicit argument
  encapsulated in the TcMonad.  -}


-- | kind check, for check = synthesis ?

-- Elaborate tm, and check that it is a well-formed type
-- at some level.
kcElab ::  Term -> TcMonad ATerm
kcElab tm = do
  (etm,ty) <- ts tm
  case (eraseToHead ty) of
    AType _ -> return etm
    _       -> err [DD tm, DS "is not a well-formed type"]

-- Check wellformedness of, and elaborate, each type in a telescope
kcTele :: Telescope -> TcMonad (Theta, ATelescope)
kcTele [] = return (Logic, [])
kcTele ((x,ty,ep):tele') = do
   ety <- kcElab ty
   th <- aGetTh ety
   (th', etele') <- extendCtx (ASig (translate x) th ety) $ kcTele tele'
   return (max th th', (translate x,ety,ep):etele')

-- | Type analysis
ta :: Term -> ATerm -> TcMonad ATerm

-- Position terms wrap up an error handler
ta (Pos p t) ty =
  extendSourceLocation p t $
    ta  t ty

ta (Paren a) ty = ta a ty

ta tm (ASubstitutedFor ty x) = ta tm ty

-- rule T_join
ta (Join s1 s2) (ATyEq a b) =
  -- The input (ATyEq a b) is already checked to be well-kinded, 
  -- so we don't need a kind-check here.
  do t1E <- erase =<< substDefs a
     t2E <- erase =<< substDefs b
     joinable <- join s1 s2 t1E t2E
     unless joinable $
       err [DS "The erasures of terms", DD a, DS "and", DD b,
            DS "are not joinable."]
     return (AJoin a s1 b s2)

    -- rule T_ord
ta (OrdAx a) (ASmaller b1 b2) = do
     (ea,tyA) <- ts a
     eaTh <- aGetTh ea
     unless (eaTh==Logic) $
       err [DS "The ordering proof", DD a, DS "should check at L but checks at P"]
     case (eaTh, eraseToHead tyA) of
       (Logic, ATyEq a1 cvs) ->
         case cvs of 
           (ADCon _ _ vs) -> do
             a1_eq_b2 <- a1 `aeqSimple` b2
             unless (a1_eq_b2) $
               err [DS "The left side of the equality supplied to ord ",
                    DS "should be", DD b2, 
                    DS "Here it is", DD a1]
             anySubterm <- anyM (\ (ai,_) -> ai `aeqSimple` b1) vs
             unless anySubterm $
                err [DS "The right side of the equality supplied to ord ",
                     DS "should be a constructor application involving", DD b1,
                     DS "Here it is", DD cvs]
             return (AOrdAx ea b1)
           _ -> err [DS "The right side of the equality supplied to ord ",
                     DS "must be a constructor application.",
                     DS "Here it is", DD cvs]
       (Logic, _) -> err [DS "The argument to ord must be an equality proof.",
                          DS "Here its type is", DD tyA]
       (Program,_) -> err [DS "The proof argument to ord must check at L, but", DD a,
                           DS "checks at P"]


-- rule T_contra
ta (Contra a) b =  do 
  -- Note, b is assumed to be already kind-checked.
   (ea, tyA) <- ts a
   eaTh <- aGetTh ea
   case (eaTh, eraseToHead tyA) of
     (Logic, ATyEq cvs1 cvs2) ->
       case (cvs1, cvs2) of
         ((ADCon c1 _ vs1), (ADCon c2 _ vs2)) ->
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
               return (AContra ea b)
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
ta (Lam lep lbody) arr@(AArrow aep abody) = do
  -- Note that the arrow type is assumed to be kind-checked already.

  --Need to do a substitution to pick the same x for both expression and type
  (dumbvar, dumbbody) <- unbind lbody
  ((x,unembed -> tyA),tyB) <- unbind abody
  let body = subst dumbvar (Var (translate x)) dumbbody

  ((dumb_x,unembed -> tyA),dumb_tyB) <- unbind abody
  (x, body) <- unbind lbody
  let tyB = subst dumb_x (AVar (translate x)) dumb_tyB

  when (lep /= aep) $
       err ([DS "Lambda annotation", DD lep,
             DS "does not match arrow annotation", DD aep])

  -- typecheck the function body
  ebody <- extendCtx (ASig (translate x) Program tyA) $
             (ta body tyB)

  -- perform the FV and value checks if in T_Lam2
  -- The free variables function fv is ad-hoc polymorphic in its
  -- return type, so we fix the type of xE.
  -- If we did (x `S.member` fv bodyE), fv would always return an empty set...
  let xE = translate x :: EName
  bodyE <- erase ebody
  when (lep == Erased && xE `S.member` fv bodyE) $
       err [DS "ta: In implicit lambda, variable", DD x,
            DS "appears free in body", DD body]

  when (lep == Erased) $ do
    unless (isEValue bodyE) $
        err [DS "ta : The body of an implicit lambda must be a value",
             DS "but here is:", DD body, DS "which erases to", DD bodyE]

  return (ALam arr lep (bind (translate x) ebody))

-- rules T_ind1 and T_ind2
ta (Ind ep lbnd) arr@(AArrow aep abnd) = do
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

      tyC = AArrow ep (bind (x, embed tyA) 
                        (AArrow Erased (bind (z, embed smallerType) xTyB)))
  -- Finally we can typecheck the fuction body in an extended environment
  (ea,eaTh) <- extendCtx (ASig (translate f) Logic tyC) $
                 extendCtx (ASig y Logic tyA) $ do
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
  return (AInd arr ep (bind (f,y) ea))

-- rules T_rec1 and T_rec2
ta (Rec ep lbnd) arr@(AArrow aep abnd) = do
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
          extendCtx (ASig y Program tyA) $
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
  return (ARec arr ep (bind (f,y) ea))

-- rule T_case
ta (Case b bnd) tyA = do
  -- premise 2, the return type must be well kinded, is assumed to be checked already.

  (y,mtchs) <- unbind bnd

  -- premises 1, 3 and 4: we check that the scrutinee is the element of some
  -- datatype defined in the context
  (eb,bty) <- ts b
  (d,bbar,delta,cons) <- lookupDType b bty
  th <- aGetTh eb

  -- premises 4 and 5: we define a function to map over the
  -- branches that checks each is OK (and elaborates it)
  unless (length mtchs == length cons) $
    err [DS "Wrong number of pattern match branches for datatype", DD d]
  let taMatch :: Match -> TcMonad AMatch
      taMatch (Match c cbnd) = do
        dumbdeltai <- lookupDCon' (translate d) (translate c)
        (deltai',ai) <- unbind cbnd
        unless (length deltai' == length dumbdeltai) $
          err [DS "wrong number of argument variables for constructor",
               DD c, DS "in pattern match."]
        unless (   map snd deltai'
                == map (\(_,_,e) -> e) dumbdeltai) $
           err [DS "wrong epsilons on argument variables for constructor",
                DD c, DS "in pattern match."]
        let deltai = aSwapTeleVars dumbdeltai (map (translate . fst) deltai')
            subdeltai = simplSubsts (zip (aDomTele delta) bbar) deltai
            eqtype = ATyEq eb (ADCon (translate c) bbar (map (\(x,_,ep) -> (AVar x, ep)) deltai))
         -- premise 5
        eai <- extendCtx (ASig (translate y) Logic eqtype) $
                           extendCtxTele subdeltai th $ ta ai tyA
        -- premise 6
        aE <- erase eai
        let yEs = translate y : map translate (aDomTeleMinus deltai)
        let shouldBeNull = S.fromList yEs `S.intersection` fv aE
        unless (S.null shouldBeNull) $
          err [DS "The constructor argument(s) and/or scrutinee equality proof",
               DD . S.toList $ shouldBeNull,
               DS "should not appear in the erasure", DD aE,
               DS "of the term", DD ai,
               DS "because they bind compiletime variables."]
        return $ AMatch (translate c) (bind (map (\(x,_,ep) -> (x,ep)) deltai) eai)         
  emtchs <- mapM taMatch mtchs
  return (ACase eb (bind (translate y) emtchs) tyA)

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
   buildCase escruts alts tyB

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
      err [DS (show y ++ " was marked as " ++ show th' ++ " but"), DD a, DS "checks at P"]

    localCtx <- getLocalCtx
    -- premise 2
    (eb,th) <- extendCtx (ASig (translate x) th' tyA) $
                 extendCtx (ASig (translate y) Logic (ATyEq (AVar (translate x)) ea)) $ do
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
    return (ALet ep (bind (translate x, translate y, embed ea) eb))

-- rule T_At
ta (At ty th') (AType i) = do 
   ea <- ta ty (AType i)
   eaTh <- aGetTh ea
   unless (eaTh <= th') $
     err [DD ty, DS "should check at L but checks at P"]
   return (AAt ea th')

-- the T_Box* rules
ta a (AAt tyA th') = do
  ea <- ta a tyA
  eaTh <- aGetTh ea
  isVal <- isValue a
  case eaTh of
    Logic                    -> return $ ABoxLL ea th'
    Program | isVal          -> return $ ABoxLV ea th'
    Program | th'==Program   -> return $ ABoxP  ea th'
    _  -> err [DD a, DS "should check at L but checks at P"]
   
ta (TerminationCase s binding) ty = err [DS "termination-case is currently unimplemented"]

ta TrustMe ty = return (ATrustMe ty)

ta InferMe (ATyEq ty1 ty2) = do
  isElaborating <- getFlag Elaborate
  unless isElaborating $
    err [DS "Trying to typecheck an InferMe when not in elaboration mode"]
  context <- getTys
  let availableEqs = 
       catMaybes $ map (\(x,th,ty) ->  case eraseToHead ty of
                                           ATyEq ty1 ty2 -> Just (x,ty1,ty2)
                                           _ -> Nothing)
                       context
  pf <- prove availableEqs (ty1,ty2)
  case pf of
    Nothing -> do
      gamma <- getLocalCtx
      err [DS "I was unable to prove:", DD (Goal (map (\(x,ty1,ty2) -> ASig x Logic (ATyEq ty1 ty2)) availableEqs) 
                                                 (ATyEq ty1 ty2)),
           DS "The full local context is", DD gamma]
    Just p -> return p

ta InferMe ty  = err [DS "I only know how to prove equalities, this goal has type", DD ty]

-- pass through SubstitutedFor
ta (SubstitutedFor a x) tyA = do
  ea <- ta a tyA
  return (ASubstitutedFor ea (translate x))

-- rule T_chk
ta a tyB = do
  --warn [DS "checking", DD a, DS ("i.e. " ++ show a), DS "against", DD tyB]
  (ea,tyA) <- ts a
  --warn [DS "got", DD tyA]
  isElaborating <- getFlag Elaborate
  tyA_eq_tyB <- tyA `aeqSimple` tyB
  if (tyA_eq_tyB)
    then return ea   --already got the right type.
    else 
     -- try to use a squash
     case maybeSquash ea tyA tyB of
       Just eaSquashed -> return eaSquashed     
       Nothing ->
        -- try to insert an equality proof.
        if isElaborating
         then do
           context <- getTys
           let availableEqs = catMaybes $ map (\(x,th,ty) -> case eraseToHead ty of
                                                               ATyEq ty1 ty2 -> Just (x, ty1, ty2)
                                                               _ -> Nothing)
                                              context
           let theGoal = (Goal (map (\(x,ty1,ty2) -> ASig x Logic (ATyEq ty1 ty2)) availableEqs) 
                                                 (ATyEq tyA tyB))
           pf <- prove availableEqs (tyA,tyB)
           case pf of 
             Nothing ->
               err [DS "When checking term", DD a, DS "against type",
                    DD tyB, DS "the distinct type", DD tyA,
                    DS "was inferred instead.",
                    DS "I was unable to prove:", DD theGoal]
             Just p -> do
                         x <- fresh (string2Name "x")
                         return $ AConv ea [(p,Runtime)] (bind [x] (AVar x)) tyB
         else err [DS "When checking term", DD a, DS "against type",
                   DD tyB,  DS ("(" ++ show tyB ++ ")"),
                   DS "the distinct type", DD tyA, DS ("("++ show tyA++")"),
                   DS "was inferred instead.",
                   DS "(Not in elaboration mode, so no automatic coersion was attempted.)"]

-- maybeSquash a tyA tyB
--  tries to insert a use of ASquash to change tyA to tyB
maybeSquash :: ATerm -> ATerm -> ATerm -> Maybe ATerm
maybeSquash a (eraseToHead -> AType l1) (eraseToHead -> AType l2) =
  if (l1 == l2)
    then Just a 
    else if (l1 < l2)
      then Just (ACumul a l2)
      else Just (ACumul (ASquash a) l2)
maybeSquash _ _ _ = Nothing

-- | Checks a list of terms against a telescope of types
-- Returns list of elaborated terms.
-- Precondition: the two lists have the same length.
taTele ::  [(Term,Epsilon)] -> ATelescope -> TcMonad [(ATerm,Epsilon)]
taTele [] [] = return []
taTele ((t,ep1):ts) ((x,ty,ep2):tele')  = do
  unless (ep1 == ep2) $
    err [DS "The term ", DD t, DS "is", DD ep1, DS "but should be", DD ep2]
  et <- ta  t ty
  ets <- taTele ts (simplSubst x et tele')
  return $ (et,ep1) : ets
taTele _ _ = error "Internal error: taTele called with unequal-length arguments"    


------------------------------
------------------------------
-------- Synthesis
------------------------------
------------------------------

-- | type synthesis
-- Returns (elaborated term, type of term)
ts :: Term -> TcMonad (ATerm,ATerm)
ts tsTm =
  do (etsTm, typ) <- ts' tsTm
     return $ (etsTm, aDelPosParenDeep typ)
  where
    ts' :: Term -> TcMonad (ATerm,ATerm)
    ts' (Pos p t) =
      extendSourceLocation p t $       
        ts' t

    ts' (Paren a) = ts' a

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
    ts' (Var y) =
      do (th',ty) <- lookupTy (translate y)
         (adjust_y, adjust_ty) <- adjustTheta (AVar (translate y)) ty
         return (adjust_y, adjust_ty)

    -- Rule T_type
    ts' (Type l) = return (AType l,  AType (l + 1))


    -- Rule T_pi
    ts' (Arrow ep body) =
      do ((x,unembed -> tyA), tyB) <- unbind body
         (etyA, tytyA) <- ts tyA
         etyATh <- aGetTh etyA
         isFO <- isFirstOrder etyA
         (etyB, tytyB) <- extendCtx (ASig (translate x) Program etyA) $ ts tyB
         case (eraseToHead tytyA, eraseToHead tytyB, isFO) of
           (AType n, AType m, True)  -> return $ (AArrow  ep  (bind (translate x,embed etyA) etyB), AType (max n m))
           (AType _, AType _, False) ->  err [DD tyA, 
                                              DS  "can not be used as the domain of a function type, must specify either",
                                              DD (At tyA Logic), DS "or", DD (At tyA Program)]
           (AType _, _, _)          -> err [DD tyB, DS "is not a type."]
           (_,_, _)                 -> err [DD tyA, DS "is not a type.", 
                                            DS "inferred", DD tytyA]

    -- Rules T_tcon and T_acon 
    ts' (TCon c args) =
      do (delta, th', lev, _) <- lookupTCon (translate c)
         unless (length args == length delta) $
           err [DS "Datatype constructor", DD c, 
                DS $ "should have " ++ show (length delta) ++
                    "parameters, but was given", DD (length args)]
         eargs <- taTele  args delta
         return (ATCon (translate c) (map fst eargs), (AType lev))

    -- Rule T_dcon
    ts' (DCon c args) = do
         (tname, delta, th', AConstructorDef _ deltai) <- lookupDCon (translate c)
         unless (length args == length delta + length deltai) $
           err [DS "Constructor", DD c,
                DS $ "should have " ++ show (length delta) ++ " parameters and " ++ show (length deltai)
                 ++ " data arguments, but was given " ++ show (length args) ++ " arguments."]
         eparams <- map fst <$> taTele (take (length delta) args) (aSetTeleEps Erased delta)
         eargs   <- taTele (drop (length delta) args) (substATele delta eparams deltai)
         return $ (ADCon (translate c) eparams eargs, ATCon tname eparams)

    -- rule T_app
    ts' tm@(App ep a b) =
      do (ea,tyArr) <- ts a
         case eraseToHead tyArr of
           AArrow epArr bnd -> do
             ((x,tyA),tyB) <- unbind bnd
             unless (ep == epArr) $
               err [DS "Application annotation", DD ep, DS "in", DD tm,
                    DS "doesn't match arrow annotation", DD epArr]

             -- check the argument, at the "A" type
             eb <- ta b (unembed tyA)

             -- Erased arguments must terminate
             when (ep==Erased) $ do
               ebTh <- aGetTh eb
               unless (ebTh==Logic) $
                 err [DS "Erased arguments must terminate, but", DD b, DS "checks at P."]

             -- check that the result kind is well-formed
             let b_for_x_in_B = simplSubst x eb tyB
             aKcAny b_for_x_in_B
             return (AApp ep ea eb b_for_x_in_B, b_for_x_in_B)
           _ -> err [DS "ts: expected arrow type, for term ", DD a,
                     DS ". Instead, got", DD tyArr]

    -- rule T_smaller
    ts' (Smaller a b) = do
      (ea,_) <- ts a
      (eb,_) <- ts b
      return $ (ASmaller ea eb, AType 0)

    -- rule T_ordtrans
    ts' (OrdTrans a b) = do
      (ea,tyA) <- ts a
      eaTh <- aGetTh ea
      unless (eaTh==Logic) $
        err [DS "The ordering proof", DD a, DS "should check at L but checks at P"]
      (eb,tyB) <- ts b
      ebTh <- aGetTh eb
      unless (ebTh== Logic) $
        err [DS "The ordering proof", DD b, DS "should check at L but checks at P"]  
      case (eraseToHead tyA, eraseToHead tyB) of 
        (ASmaller a1 a2, ASmaller b1 b2) -> do
          a2_eq_b1 <- a2 `aeqSimple` b1
          unless (a2_eq_b1) $
            err [DS "The middle terms of the inequalities given to ordtrans must match, ",
                 DS "but here they are", DD a2, DS "and", DD b1]
          return $ (AOrdTrans ea eb, ASmaller a1 b2)
        _ -> err [DS "The arguments to ordtrans must be proofs of <, ",
                  DS "here they have types", DD tyA, DS "and", DD tyB]

    -- rule T_eq
    ts' (TyEq a b) = do
      (ea,_) <- ts a
      (eb,_) <- ts b
      return $ (ATyEq ea eb, AType 0)

    -- rule T_conv
    -- Elaborating this is complicated, because we use two different strategies for the Runtime and Erased
    -- elements of as. For Runtime elements we synthesize a type and and elaborated term in one go.
    -- For Erased ones, we substitute them into the template c, elaborate the template, and then dig out the 
    -- elaborated a from the elaborated template.
    ts' (Conv b as bnd) =
      do (xs,c) <- unbind bnd
         let chkTy (pf,Runtime) x = do
               (epf,pfTy) <- ts pf
               pfTh <- aGetTh epf
               unless (pfTh==Logic) $
                 err [DS "equality proof", DD pf, DS "should check at L but checks at P"]
               case eraseToHead pfTy of
                ATyEq tyA1 tyA2 -> return $ (Just epf, SubstitutedForA tyA1 x, SubstitutedForA tyA2 x)
                _ -> err $ [DS "The second arguments to conv must be equality proofs,",
                            DS "but here has type", DD pfTy]
             chkTy (isTyEq -> Just (tyA1,tyA2) ,Erased) x = do
               return (Nothing, SubstitutedFor tyA1 x, SubstitutedFor tyA2 x)
             chkTy (pf, Erased) _ = 
                err [DS "erased conv proofs should be equalities, but here it is", DD pf]
         atys <- zipWithM chkTy as xs


         let cA1 = simplSubsts (zip xs (map (\(_,x,_)->x) atys)) c
         ecA1 <- kcElab cA1
         let cA2 = simplSubsts (zip xs (map (\(_,_,x)->x) atys)) c
         ecA2 <- kcElab cA2
        
         eb <- ta b ecA1

         let exs = map translate xs
         let ec = unsubstitute ecA2
         let lhss = extractSubstitution ecA1
         let rhss = extractSubstitution ecA2
         let elaborateProof (Just ea, _,_) x = return (ea, Runtime)
             elaborateProof (Nothing, _,_) x =
               case (M.lookup x lhss, M.lookup x rhss) of
                 (Just etyA1, Just etyA2) -> return (ATyEq etyA1 etyA2, Erased)
                 _ -> err [DS "The variable", DD x, DS "does not occur in the conv template expression"]
         eas <- zipWithM elaborateProof atys exs

         erasedEc <- erase ec
         let chkErased (pf,Runtime) _ = return ()
             chkErased (pf,Erased) var = do
               when (translate var `S.member` fv erasedEc) $
                   err [DS "Equality proof", DD pf, DS "is marked erased",
                        DS "but the corresponding variable", DD var,
                        DS "appears free in the erased term", DD erasedEc]
         zipWithM_ chkErased as xs

         return (AConv eb eas (bind exs ec) ecA2, ecA2)

    -- rule T_annot
    ts' (Ann a tyA) =
      do etyA <- kcElab tyA
         ea <- ta a etyA
         return (ea, etyA)

    -- pass through SubstitutedFor
    ts' (SubstitutedFor a x) =
     do (ea,tyA) <- ts' a
        return (ASubstitutedFor ea (translate x), tyA)

    -- pass through SubstitutedForA
    ts' (SubstitutedForA ea x) = do
      (th, eaTy) <- aTs ea
      return (ASubstitutedFor ea (translate x), eaTy)

    -- the synthesis version of rules T_let1 and T_let2
    ts' (Let th' ep bnd) =
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
        (eb,tyB) <- extendCtx (ASig (translate y) Logic (ATyEq (AVar (translate x)) ea)) $
                      extendCtx (ASig (translate x) th' tyA) $
                        ts b
        -- premise 3
        aKcAny tyB

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
        return (ALet ep (bind (translate x, translate y,embed ea) eb), tyB)

    -- T_at
    ts' (At tyA th') = do
      (ea, s) <- ts tyA
      eaTh <- aGetTh ea
      unless (eaTh <= th') $
        err [DS "The type", DD tyA, DS "should check at L but checks at P"]
      return (AAt ea th', s)

    -- Elaborating 'unfold' directives.
    ts' (Unfold n a) = do
      (ea, _) <- ts a
      err [DS "Unfortunately unfold is not implemented, because it poses unsolvable fundamental problems."]
      -- return (Ann (Join n n) (TyEq 

    ts' tm = err $ [DS "Sorry, I can't infer a type for:", DD tm,
                    DS "Please add an annotation.",
                    DS "NB: This error happens when you misspell,",
                    DS "so check your spelling if you think you did annotate."]

-- | Take an annotated term which typechecks at aTy, and try to
--   apply as many Unboxing/Firstorder rules as possible.
adjustTheta :: ATerm -> ATerm -> TcMonad (ATerm, ATerm)
adjustTheta a aTy = do
  isVal <- isEValue <$> erase a
  if isVal 
    then case eraseToHead aTy of
      (AAt ty' th') -> adjustTheta (AUnboxVal a) ty'
      _  -> do
        aTh <- aGetTh a
        if aTh == Logic
          then return (a, aTy)
          else do
            isFo <- isFirstOrder aTy
            if isFo
               then return (AFO a, aTy)
               else return (a, aTy)
    else return (a, aTy)

--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each modules
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked and elaborated into the core
-- language.
tcModules :: [Module] -> TcMonad [AModule]
tcModules mods = foldM tcM [] mods
  -- Check module m against modules in defs, then add m to the list.
  where defs `tcM` m = do -- "M" is for "Module" not "monad"
          let name = moduleName m
          liftIO $ putStrLn $ "Checking module " ++ show name
          m' <- defs `tcModule` m
          return $ defs++[m']

-- | Typecheck an entire module.
tcModule :: [AModule]        -- ^ List of already checked modules (including their Decls).
         -> Module           -- ^ Module to check.
         -> TcMonad AModule  -- ^ The same module with all Decls checked and elaborated.
tcModule defs m' = do checkedEntries <- extendCtxMods importedModules $
                                          foldr tcE (return [])
                                                  (moduleEntries m')
                      return $ AModule (moduleName m') checkedEntries
  where d `tcE` m = do
          -- Extend the Env per the current Decl before checking
          -- subsequent Decls.
          x <- tcEntry d
          case x of
            AddHint  hint  -> extendHints hint m
                           -- Add decls to the Decls to be returned
            AddCtx decls -> (decls++) <$> (extendCtxsGlobal decls m)
        -- Get all of the defs from imported modules (this is the env to check current module in)
        importedModules = filter (\x -> (ModuleImport (aModuleName x)) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Decl.
data HintOrCtx = AddHint AHint
               | AddCtx [ADecl]
                 -- Q: why [ADecl] and not ADecl ? A: when checking a
                 -- Def w/o a Sig, a Sig is synthesized and both the
                 -- Def and the Sig are returned.

tcEntry :: Decl -> TcMonad HintOrCtx

tcEntry (Def n term) = do
  oldDef <- lookupDef (translate n)
  case oldDef of
    Nothing -> tc
    Just term' -> die term'
  where
    tc = do
      lkup <- lookupHint (translate n)
      case lkup of
        Nothing -> do (eterm,ty) <- ts term
                      th <- aGetTh eterm
                      -- Put the elaborated version of term into the context.
                      return $ AddCtx [ASig (translate n) th ty, ADef (translate n) eterm]
        Just (theta,ty) ->
          let handler (Err ps msg) = throwError $ Err (ps) (msg $$ msg')
              msg' = disp [DS "When checking the term ", DD term,
                           DS "against the signature", DD ty]
          in do
            eterm <- ta term ty `catchError` handler
            etermTh <- aGetTh eterm
            unless (etermTh <= theta) $
              err [DS "The variable", DD n, DS "was marked as L but checks at P"]
            -- If we already have a type in the environment, due to a sig
            -- declaration, then we don't add a new signature.
            --
            -- Put the elaborated version of term into the context.
            return $ AddCtx [ASig (translate n) theta ty, ADef (translate n) eterm]
    die term' =
      extendSourceLocation (unPosFlaky term) term $
         err [DS "Multiple definitions of", DD n,
              DS "Previous definition was", DD term']

tcEntry (Sig n th ty) = do
  duplicateTypeBindingCheck n ty
  ety <- kcElab ty
  tyTh <- aGetTh ety
  unless (tyTh <= th) $
    err [DS "The variable", DD n, DS "was marked as L, but", DD ty, DS "checks at P"]
  return $ AddHint (AHint (translate n) th ety)

tcEntry (Axiom n th ty) = do
  duplicateTypeBindingCheck n ty
  ety <- kcElab ty
  tyTh <- aGetTh ety
  unless (tyTh <= th) $
    err [DS "The variable", DD n, DS "was marked as L, but", DD ty, DS "checks at P"]
  return $ AddCtx [ASig (translate n) th ety, 
                   ADef (translate n) (ATrustMe ety)]

-- rule Decl_data
tcEntry (Data t delta th lev cs) =
  do -- The parameters of a datatype must all be Runtime.
     unless (all (\(_,_,ep) -> ep==Runtime) delta) $
       err [DS "All parameters to a datatype must be marked as relevant."]
     ---- Premise 1
     (edeltaTh, edelta) <- kcTele delta
     unless (edeltaTh <= th) $
       err [DS "The telescope", DD delta, DS "is marked as L but checks at P"]
     ---- Premise 2: check that the telescope provided 
     ---  for each data constructor is wellfomed, and elaborate them
     ---  fixme: probably need to worry about universe levels also?
     let elabConstructorDef defn@(ConstructorDef pos d tele) =
            extendSourceLocation pos defn $ 
              extendCtx (AAbsData (translate t) edelta th lev) $
                extendCtxTele edelta th $ do
                  (teleTh, etele) <- kcTele tele  --Fixme: need to use this teleTh also.
                  return (AConstructorDef (translate d) etele)
     ecs <- mapM elabConstructorDef cs
     -- Premise 3: check that types are strictly positive.
     when (th == Logic) $
       mapM_ (positivityCheck t) cs
     -- Implicitly, we expect the constructors to actually be different...
     let cnames = map (\(ConstructorDef _ c _) -> c) cs
     unless (length cnames == length (nub cnames)) $
       err [DS "Datatype definition", DD t, DS"contains duplicated constructors" ]
     -- finally, add the datatype to the env and perform action m
     return $ AddCtx [AData (translate t) edelta th lev ecs]

tcEntry dt@(AbsData t delta th lev) = do
  (edeltaTh, edelta) <- kcTele delta
  unless (edeltaTh <= th) $
    err [DS "The telescope", DD delta, DS "is marked as L but checks at P"]
  return $ AddCtx [AAbsData (translate t) edelta th lev]

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
         extendSourceLocation p ty $ err msg

isFirstOrder :: ATerm -> TcMonad Bool
isFirstOrder ty = isFirstOrder' S.empty ty
  where
    isFirstOrder' :: Set AName -> ATerm -> TcMonad Bool
    isFirstOrder' _ (eraseToHead -> ATyEq _ _) = return True
    isFirstOrder' _ (eraseToHead -> ASmaller _ _) = return True
    isFirstOrder' _ (eraseToHead -> AAt _ _) = return True
    isFirstOrder' s (eraseToHead -> ATCon d _) | d `S.member` s = return True
    isFirstOrder' s (eraseToHead -> ATCon d _) = do
      ent <- lookupTCon d
      case ent of
        (_,_,_,Nothing)  -> 
          --An abstract datatype constructor. Maybe this is too conservative?
          return False
        (_,_,_,Just cons) -> 
          -- Datatypes are FO if all components are. But in order to not get caught in an
          -- infinite loop, we should probably give the constructor d the "benefit of the
          -- doubt"  while doing so...
          allM (\(AConstructorDef _ args) -> allM (\(_,ty,_) -> isFirstOrder' (S.insert d s) ty) args) cons 
    isFirstOrder' _ (eraseToHead -> AAt _ _) = return True
    isFirstOrder' _ _ = return False
    
-- Positivity Check

-- | Determine if a data type only occurs in strictly positive positions in a
-- constructor's arguments.

positivityCheck
  :: (Fresh m, MonadError Err m, MonadReader Env m) =>
     Name Term -> ConstructorDef -> m ()
positivityCheck tName (ConstructorDef _ cName tele)  = do
  mapM_ checkBinding tele
   `catchError` \(Err ps msg) ->  throwError $ Err ps (msg $$ msg')
  where checkBinding (_,teleTy,_) = occursPositive tName teleTy
        msg' = text "When checking the constructor" <+> disp cName

occursPositive  :: (Fresh m, MonadError Err m, MonadReader Env m) => 
                   Name Term -> Term -> m ()
occursPositive tName (Pos p ty) = do
  extendSourceLocation p ty $
    occursPositive tName ty 
occursPositive tName (Paren ty) = occursPositive tName ty
occursPositive tName (Arrow _ bnd) = do
 ((_,etyA), tyB) <- unbind bnd
 let tyA = unembed etyA
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
           (delta,_,_,Just cons) ->
             do unless (length params == length delta) $
                   err [DS "Attempted to match against", DD b,
                        DS "with type", DD bty, DS "where", DD d,
                        DS "is applied to the wrong number of arguments."]
                return (d, params, delta, cons)
           (_,_,_,Nothing) ->
              err [DS "Scrutinee ", DD b,
                   DS "is a member of an abstract datatype - you may not",
                   DS "pattern match on it."]
lookupDType b bty = err [DS "Scrutinee ", DD b,
                         DS "must be a member of a datatype, but is not. It has type", DD bty]

-- | (lookupDCon' d c) finds the arguments of constructor c, which should be one of the constructors of d.
lookupDCon' :: AName -> AName -> TcMonad ATelescope
lookupDCon' d c = do
  dDef <- lookupTCon d
  case dDef of 
    (_,_,_,Just cons) -> 
       case find (\(AConstructorDef  c' _) -> c'==c) cons of
         Nothing -> err [DD c, DS "is not a constructor of type", DD d]
         Just (AConstructorDef _ deltai)  -> return deltai
    _ -> err [DD c, DS "is not a constructor of type", DD d]

--------------------------------------
-- Simplifying substitution
--------------------------------------

{- Suppose that somewhere inside a typing derivation we have
   (AUnboxVal x) for some variable x, and then want to substitute
   (ABox a) for x, where a is some non-value expression.  If we just
   constructed the derivation (AUnboxVal (ABox a)) it would violate
   the value restriction of Unbox.

   This case is actually very common for the regularity premise of the
   function application rule. In the case when a function
   argument has an @-type, we implicitly use Unbox to check that the
   function type is well-kinded, and also implicitly use Box at the
   call site to give the argument the right type. So it's
   important to do something about this.

   Here, I define a function to simplify away such Unbox-Box pairs.

   Probably one should try harder than this, but more sophisticated 
   simplifications would require type information.
 -}


simplUnboxBox :: Rep a => a -> a
simplUnboxBox = RL.everywhere (RL.mkT simplUnboxBoxOnce)
  where simplUnboxBoxOnce :: ATerm -> ATerm 
        simplUnboxBoxOnce (AUnboxVal (ABoxLL a Logic)) = a
        simplUnboxBoxOnce (AUnboxVal (ABoxLL a Program)) = a
        simplUnboxBoxOnce (AUnboxVal (ABoxLV a _)) = a
        simplUnboxBoxOnce (AUnboxVal (ABoxP a _)) = a
        simplUnboxBoxOnce a = a

simplSubst :: Subst b a => Name b -> b -> a -> a
simplSubst x b a = simplUnboxBox $ subst x b a

simplSubsts :: Subst b a => [(Name b, b)] -> a -> a
simplSubsts xs a =  simplUnboxBox $ substs xs a

---------------------------------------
-- Some random utility functions
---------------------------------------

freshATele :: (Functor m, Fresh m) => ATelescope -> m ATelescope
freshATele [] = return []
freshATele ((x,ty,ep):t) = do
   x' <- fresh x
   t' <- freshATele (subst x (AVar x') t)
   return $ (x',ty,ep):t'

-- | (substATele bs delta a) substitutes the b's for the variables in delta in a.
-- Precondition: bs and delta have the same lenght.
substATele :: Subst ATerm a => ATelescope -> [ATerm] -> a -> a
substATele [] [] a = a
substATele  ((x,ty,ep):tele) (b:bs) a = substATele tele bs (simplSubst x b a)

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

-- (buildCase scrutinees scrutineeTys alts tyAlt) builds a case tree that
-- evaluates to the first alternative that matches, or 'fallback' if
-- none of them do. The argument scrutineeTys is a list of the types of the scrutinees.
-- Each branch in alts should have type tyAlt.
--
-- precondition: scrutineeTys has the same length as scrutinees, and all the pattern lists have the same length 
-- as scrutinees.
--
--            scrutinee  equation-name    branches          branch-type
buildCase :: [(ATerm,    TName)]       -> [ComplexMatch] -> ATerm        -> TcMonad ATerm
buildCase [] [] _ = err [DS "Patterns in case-expression not exhaustive."]
buildCase [] ((ComplexMatch bnd):_) tyAlt = do
  ([], body) <- unbind bnd  --no more patterns to match.
  ta body tyAlt
buildCase ((s,y):scruts) alts tyAlt | not (null alts) && not (isAVar s) && any isEssentialVarMatch alts = do
  -- If one of the branches contains an isolated variable, the ComplexCase basically acts as
  --  a let-expression, so that's what we elaborate it into.
  x <- fresh (string2Name "_scrutinee")
  x_eq <- fresh (string2Name "_")
  (th,sTy) <- aTs s
  (ALet Runtime . bind (x, x_eq, embed s)) <$>
    (extendCtx (ASig x th sTy) $
      extendCtx (ASig x_eq Logic (ATyEq (AVar x) s)) $
        buildCase ((AVar x,y):scruts) alts tyAlt)
buildCase ((s,y):scruts) alts tyAlt | not (null alts) && all isVarMatch alts = do
  --Todo: handle the scrutinee=pattern equation y somehow?
  alts' <- mapM (expandMatch s [] <=< matchPat) alts
  buildCase scruts alts' tyAlt
buildCase ((s,y):scruts) alts tyAlt = do
  (th,sTy) <- aTs s
  (d, bbar, delta, cons) <- lookupDType s sTy
  let buildMatch :: AConstructorDef -> TcMonad AMatch
      buildMatch (AConstructorDef c args) = do
        relevantAlts <- filter (\(p,_) -> case p of 
                                           (PatCon (unembed -> c') _) -> (translate c')==c
                                           (PatVar _) -> True)
                           <$> mapM matchPat alts

        args' <- freshATele args --This may look silly, but we don't get it fresh for free.
        newScruts <- mapM (\(x,_,_) -> ((AVar (translate x)), ) <$> (fresh $ string2Name "_")) args'
        let newScrutTys = map (\(x,ty,_) -> (x,ty)) $ simplSubsts (zip (aDomTele delta) bbar) args'
        newAlts <- mapM (expandMatch s args') relevantAlts
        let erasedVars = (S.fromList $ catMaybes $ map (\(x,ty,ep) -> if ep==Erased then Just x else Nothing) args')
                         `S.union` (S.singleton (translate y))
        newBody <- extendCtxs (reverse $ map (\(x,ty) -> ASig x th ty) newScrutTys) $ 
                     extendCtx (ASig (translate y) Logic 
                                     (ATyEq s (ADCon c bbar (map (\(x,_,ep)->(AVar x,ep)) args')))) $
                       buildCase (newScruts++scruts) newAlts tyAlt
        erasedNewBody <- erase newBody
        unless (S.null (S.map translate (fv erasedNewBody) `S.intersection` erasedVars)) $ do
          let (x:_) = S.toList (fv newBody `S.intersection` erasedVars)
          err [DS "The variable", DD x, DS "is marked erased and should not appear in the erasure of the case expression"]
        return $ AMatch c (bind (map (\(x,_,ep) -> (x,ep)) args') newBody)
  ematchs <- bind (translate y) <$> mapM buildMatch cons
  return $ ACase s ematchs tyAlt

-- | expandMatch scrut args (pat, alt) 
-- adjusts the ComplexMatch 'alt'
-- for the fact that 'scrut' has just been sucessfully tested against
-- pattern pat.  It adds the new variables args to the list of
-- patterns for alt, and substitutes scrut into the body of alt if
-- 'pat' was a variable pattern.a
-- Precondition: scrut is a variable (so we can substitute it into the body).

expandMatch :: ATerm ->  ATelescope -> (Pattern, ComplexMatch) -> TcMonad ComplexMatch
expandMatch s  args (PatCon (unembed -> c) newPats, ComplexMatch alt) = do
  unless (length newPats == length args) $ 
    err [DS "constructor", DD c, DS $ "should take " ++ show (length args) ++ " constructors,",
         DS "but the pattern", DD (PatCon (embed c) newPats), DS $ "has " ++ show (length newPats) ++ "."]
  unless (map (\(_,_,ep)->ep) args == map snd newPats) $
    err [DS "wrong epsilons on arguments in pattern", DD (PatCon (embed c) newPats)]
  (pats, body) <- unbind alt
  return $ ComplexMatch (bind (map fst newPats++pats) body)
expandMatch s args (PatVar z, ComplexMatch alt) = do
  newPats <- mapM (\(_,_,ep) -> do x <- fresh (string2Name  "_"); return (PatVar x, ep)) args
  (pats, body) <- unbind alt
  --Avoid introducing a let-binding in the case when the scrutinee is already a variable:
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
