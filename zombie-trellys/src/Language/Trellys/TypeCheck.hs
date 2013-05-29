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
import Language.Trellys.AOpSem (astep, asteps)

import Language.Trellys.Options
import Language.Trellys.Environment
import Language.Trellys.Error
import Language.Trellys.TypeMonad
import Language.Trellys.EqualityReasoning
import Language.Trellys.TypeCheckCore

import Generics.RepLib.Lib(subtrees)
import Text.PrettyPrint.HughesPJ

import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad.Reader hiding (join)
import Control.Monad.Error  hiding (join)
--import Control.Monad.State  hiding (join)
import Control.Arrow ((&&&), Kleisli(..))

import qualified Generics.RepLib as RL

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
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

-- Check wellformedness of, and elaborate, each type in a telescope
kcTele :: Telescope -> TcMonad ATelescope
kcTele [] = return AEmpty
kcTele ((x,ty,ep):tele') = do
   ety <- kcElab ty
   unless (isFirstOrder ety) $
     err [DS "Each type in a telescope needs to be first-order, but", DD ty, DS "is not"]
   etele' <- extendCtx (ASig (translate x) Program ety) $ kcTele tele'
   return (ACons (rebind (translate x,embed ety,ep) etele'))

-- | Type analysis
ta :: Term -> ATerm -> TcMonad ATerm

-- Position terms wrap up an error handler
ta (Pos p t) ty =
  extendSourceLocation p t $
    ta  t ty

ta (Paren a) ty = ta a ty

ta tm (ASubstitutedFor ty x) = ta tm ty

ta (UniVar x) ty = return (AUniVar (translate x) ty)
  --currently all univars in the source program are distinct, 
  -- so we don't have to check for a binding of x.

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

     aSubst <- substDefs a
     testReduction aSubst
     --testReduction bSubst
     --printReductionPath aSubst
     return (AJoin a s1 b s2)

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
                     DS "Here it is", DD cvs]
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
ta (Lam lep lbody) arr@(AArrow _ ex aep abody) = do
  -- Note that the arrow type is assumed to be kind-checked already.

  -- Can't use unbind2 because lbody and abody bind names from 
  -- different languages.
  ((dumb_x,unembed -> tyA),dumb_tyB) <- unbind abody
  (x, body) <- unbind lbody
  let tyB = subst dumb_x (AVar (translate x)) dumb_tyB

  when (lep /= aep) $
       err ([DS "Lambda annotation", DD lep,
             DS "does not match arrow annotation", DD aep])

  -- typecheck the function body
  ebody <- extendCtx (ASig (translate x) Program tyA) $
             (ta body tyB)
             
  -- get the theta from the annotated body           
  (th,_) <- getType ebody  

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
  return (ALam th zarr lep (bind (translate x) ebody))

-- rules T_ind1 and T_ind2
ta (Ind ep lbnd) arr@(AArrow k ex aep abnd) = do
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
  zarr <- zonkTerm arr
  return (AInd zarr ep (bind (f,y) ea))

-- rules T_rec1 and T_rec2
ta (Rec ep lbnd) arr@(AArrow k ex aep abnd) = do
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
  zarr <- zonkTerm arr
  return (ARec zarr ep (bind (f,y) ea))

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
      err [DS (show y ++ " was marked as " ++ show th' ++ " but"), DD a, DS "checks at P"]

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
    zea <- zonkTerm ea
    return (ALet ep (bind (translate x, translate y, embed zea) eb))

    -- Elaborating 'unfold' directives; checking version

ta (Unfold n a b) tyB = do
   (ea, _) <- ts a
   ea' <- asteps n ea 
   x   <- fresh $ string2Name "steps"
   y   <- fresh $ string2Name "_"
   eb  <- extendCtx (ASig x Logic (ATyEq ea ea'))
            $ ta b tyB      
   return (ALet Runtime (bind (x, y, embed (AJoin ea n ea' 0)) eb))

-- rule T_At
ta (At ty th') (AType i) = do 
   ea <- ta ty (AType i)
   eaTh <- aGetTh ea
   unless (eaTh == Logic) $
     err [DD ty, DS "should check at L but checks at P"]
   return (AAt ea th')

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
   
ta (TerminationCase s binding) ty = err [DS "termination-case is currently unimplemented"]

ta TrustMe ty = return (ATrustMe ty)

ta InferMe (ATyEq ty1 ty2) = do
  availableEqs <- getAvailableEqs
  pf <- prove availableEqs (ty1,ty2)
  case pf of
    Nothing -> do
      gamma <- getLocalCtx
      err [DS "I was unable to prove:", DD (Goal (map (\(x,tyLHS,tyRHS) -> (x, (ATyEq tyLHS tyRHS))) availableEqs)
                                                 (ATyEq ty1 ty2)),
           DS "The full local context is", DD gamma]
    Just p -> do
       pE <- erase p
       if (S.null (fv pE :: Set EName))
         then zonkTerm p
         else zonkTerm =<< (uneraseTerm ty1 ty2 p)       

ta InferMe ty  = err [DS "I only know how to prove equalities, this goal has type", DD ty]

-- pass through SubstitutedFor
ta (SubstitutedFor a x) tyA = do
  ea <- ta a tyA
  return (ASubstitutedFor ea (translate x))

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
           let theGoal = (Goal (map (\(x,ty1,ty2) -> (x, (ATyEq ty1 ty2))) availableEqs) 
                               (ATyEq tyA ztyB))
           pf <- prove availableEqs (tyA,ztyB)
           case pf of 
             Nothing ->
               err [DS "When checking term", DD a, DS "against type",
                    DD tyB,  DS ("(" ++ show tyB ++ ")"),
                    DS "the distinct type", DD tyA, DS ("(" ++ show tyA ++"("),
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
                         x <- fresh (string2Name "x")
                         zonkTerm $ AConv ea [(p,Runtime)] (bind [x] (AVar x)) ztyB
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

-- | Checks a list of terms against a telescope of types
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
    err [DS "Each argument needs to check logically, but", DD t, DS "checks at P"]
  eterms <- taLogicalTele terms (simplSubst x et tele')
  zet <- zonkTerm et
  return $ (zet,ep1) : eterms
taLogicalTele _ _ = error "Internal error: taTele called with unequal-length arguments"    


-- | Checks a list of terms against a telescope of types,
-- with the proviso that each term needs to check at Logic.
-- Returns list of elaborated terms.
-- Precondition: the two lists have the same length.
--
-- Unlike ta, here the telescope is not assumed to already be zonked.
taTele ::  [(Term,Epsilon)] -> ATelescope -> TcMonad [(ATerm,Epsilon)]
taTele [] AEmpty = return []
taTele ((t,ep1):terms) (ACons (unrebind->((x,unembed->ty,ep2),tele')))  = do
  unless (ep1 == ep2) $
    err [DS "The term ", DD t, DS "is", DD ep1, DS "but should be", DD ep2]
  zty <- zonkTerm ty
  et <- ta  t zty
  --Fixme: need to check that erased arguments are logical.
  eterms <- taTele terms (simplSubst x et tele')
  zet <- zonkTerm et
  return $ (zet,ep1) : eterms
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
      do (th,ty) <- lookupTy (translate y)
         zty <- zonkTerm ty
         (_, adjust_y, adjust_ty) <- adjustTheta th (AVar (translate y)) zty
         return (adjust_y, adjust_ty)

    -- Rule T_type
    ts' (Type l) = return (AType l,  AType (l + 1))


    -- Rule T_pi
    ts' (Arrow ex ep body) =
      do ((x,unembed -> tyA), tyB) <- unbind body
         (etyA, tytyA) <- ts tyA
         etyATh <- aGetTh etyA
         (etyB, etyBTh, tytyB) <- extendCtx (ASig (translate x) Program etyA) $ do 
                                                                                  (etyB, tytyB) <- ts tyB
                                                                                  etyBTh <- aGetTh etyB
                                                                                  return (etyB, etyBTh, tytyB)
         unless (etyATh == Logic) $
            err [DS "domain of an arrow type must check logically, but", DD tyA, DS "checks at P"]
         unless (etyBTh == Logic) $
            err [DS "domain of an arrow type must check logically, but", DD tyB, DS "checks at P"]
         case (eraseToHead tytyA, eraseToHead tytyB, isFirstOrder etyA) of
           (AType n, AType m, True)  -> return $ (AArrow (max n m) ex ep  (bind (translate x,embed etyA) etyB), AType (max n m))
           (AType _, AType _, False) ->  err [DD tyA, 
                                              DS  "can not be used as the domain of a function type, must specify either",
                                              DD (At tyA Logic), DS "or", DD (At tyA Program)]
           (AType _, _, _)          -> err [DD tyB, DS "is not a type."]
           (_,_, _)                 -> err [DD tyA, DS "is not a type.", 
                                            DS "inferred", DD tytyA]

    -- Rules T_tcon and T_acon 
    ts' (TCon c args) =
      do (delta, lev, _) <- lookupTCon (translate c)
         unless (length args == aTeleLength delta) $
           err [DS "Datatype constructor", DD c, 
                DS $ "should have " ++ show (aTeleLength delta) ++
                    " parameters, but was given", DD (length args)]
         eargs <- taLogicalTele args delta
         return (ATCon (translate c) (map fst eargs), (AType lev))

    -- Rule D | _dcon
    ts' (DCon c args) = do
         (tname, delta, AConstructorDef _ deltai) <- lookupDCon (translate c)
         unless (length args == aTeleLength delta + aTeleLength deltai) $
           err [DS "Constructor", DD c,
                DS $ "should have " ++ show (aTeleLength delta) ++ " parameters and " ++ show (aTeleLength deltai)
                 ++ " data arguments, but was given " ++ show (length args) ++ " arguments."]
         eparams <- map fst <$> taTele (take (aTeleLength delta) args) (aSetTeleEps Erased delta)
         eargs <- taTele (drop (aTeleLength delta) args) (substATele delta eparams deltai)
         zeparams <- mapM zonkTerm eparams
         aKc (ATCon tname zeparams)
         return $ (ADCon (translate c) Logic zeparams eargs, ATCon tname zeparams)

    -- rule T_app
    ts' tm@(App ep a b) =
      do (eaPreinst, tyPreinst) <- ts a
         (ea,tyArr) <- instantiateInferreds eaPreinst tyPreinst        
         case eraseToHead tyArr of
           AArrow _ ex epArr bnd -> do
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

             zea <- zonkTerm ea
             ztyB <- zonkTerm tyB

             -- check that the result kind is well-formed
             let b_for_x_in_B = simplSubst x eb ztyB
             aKc b_for_x_in_B
             return (AApp ep zea eb b_for_x_in_B, b_for_x_in_B)
           _ -> err [DS "ts: expected arrow type, for term ", DD a,
                     DS ". Instead, got", DD tyArr]

    -- rule T_smaller
    ts' (Smaller a b) = do
      (ea,_) <- ts a
      (eb,_) <- ts b
      zea <- zonkTerm ea
      return $ (ASmaller zea eb, AType 0)

    -- rule T_ordtrans
    ts' (OrdTrans a b) = do
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
    ts' (TyEq a b) = do
      (ea,_) <- ts a
      (eb,_) <- ts b
      zea <- zonkTerm ea
      return $ (ATyEq zea eb, AType 0)

    -- rule T_conv
    -- Elaborating this is complicated, because we use two different strategies for the Runtime and Erased
    -- elements of as. For Runtime elements we synthesize a type and and elaborated term in one go.
    -- For Erased ones, we substitute them into the template c, elaborate the template, and then dig out the 
    -- elaborated a from the elaborated template.

--Todo: zonking. This is slightly involved, since there are many subterms.
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

-- Datatype injectivity. This is rough-and-ready, since it will be merged into the 
-- congruence closure implementation rather than being exposed in the surface language.
    ts' (InjDCon a i) =
      do (ea,_) <- ts a
         (_, ty) <- aTs (AInjDCon ea i)
         return (AInjDCon ea i, ty)

    -- rule T_annot
    ts' (Ann a tyA) =
      do etyA <- kcElab tyA
         ea <- ta a etyA
         zetyA <- zonkTerm etyA
         return (ea, zetyA)

    -- pass through SubstitutedFor
    ts' (SubstitutedFor a x) =
     do (ea,tyA) <- ts' a
        return (ASubstitutedFor ea (translate x), tyA)

    -- pass through SubstitutedForA
    ts' (SubstitutedForA ea x) = do
      (th, eaTy) <- aTs ea
      zea <- zonkTerm ea
      return (ASubstitutedFor zea (translate x), eaTy)

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
        return (ALet ep (bind (translate x, translate y,embed zea) eb), tyB)

    -- T_at
    ts' (At tyA th') = do
      (ea,s) <- ts tyA
      eaTh <- aGetTh ea
      case (eaTh,eraseToHead s) of
        (Logic, AType i) -> return (AAt ea th',s)
        (Program,AType i) -> err [DS "Types should check at L, but", DD tyA, DS "checks at P"]
        (_,_)             -> err [DS "Argument to @ should be a type, here it is", DD tyA, DS "which has type", DD s]

    -- Elaborating 'unfold' directives; synthesising version
    ts' (Unfold n a b) = do
      (ea, _) <- ts a
      ea' <- asteps n ea 
      x <- fresh $ string2Name "steps"
      y <- fresh $ string2Name "_"
      (eb,tyB) <- extendCtx (ASig x Logic (ATyEq ea ea'))
                    $ ts b      
      return (ALet Runtime (bind (x, y, embed (AJoin ea n ea' 0)) eb), tyB)

    ts' tm = err $ [DS "Sorry, I can't infer a type for:", DD tm,
                    DS "Please add an annotation.",
                    DS "NB: This error happens when you misspell,",
                    DS "so check your spelling if you think you did annotate."]

-- | Take an annotated term which typechecks at aTy, and try to
--   apply as many Unboxing rules as possible.
adjustTheta :: Theta -> ATerm -> ATerm -> TcMonad (Theta, ATerm, ATerm)
adjustTheta th a aTy = do
  isVal <- isEValue <$> erase a
  if isVal 
    then case eraseToHead aTy of
      (AAt ty' th') -> adjustTheta th' (AUnboxVal a) ty'
      _  -> return (th, a, aTy)
    else return (th, a, aTy)

-- | Take a term which perhaps has an inferred arrow type (that is, (x1:A1)=>...(xn:An)=>B), 
-- and replace the xs with unification variables.
instantiateInferreds :: ATerm -> ATerm -> TcMonad (ATerm,ATerm)
instantiateInferreds a (eraseToHead -> AArrow _ Inferred ep bnd) = do
  ((x,unembed->aTy),bTy) <- unbind bnd
  u <- AUniVar <$> (fresh (string2Name "")) <*> (pure aTy)
  let bTy' = subst x u bTy
  instantiateInferreds (AApp ep a u bTy') bTy'
instantiateInferreds a aTy = return (a, aTy)

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
tcEntry (Data t delta lev cs) =
  do -- The parameters of a datatype must all be Runtime.
     unless (all (\(_,_,ep) -> ep==Runtime) delta) $
       err [DS "All parameters to a datatype must be marked as relevant."]
     ---- Premise 1
     edelta <- kcTele delta
     ---- Premise 2: check that the telescope provided 
     ---  for each data constructor is wellfomed, and elaborate them
     ---  fixme: probably need to worry about universe levels also?
     let elabConstructorDef defn@(ConstructorDef pos d tele) =
            extendSourceLocation pos defn $ 
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
     return $ AddCtx [AData (translate t) edelta lev ecs]

tcEntry dt@(AbsData t delta lev) = do
  edelta <- kcTele delta
  return $ AddCtx [AAbsData (translate t) edelta lev]

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

isFirstOrder :: ATerm -> Bool
isFirstOrder (eraseToHead -> ATyEq _ _)    =  True
isFirstOrder (eraseToHead -> ASmaller _ _) =  True
isFirstOrder (eraseToHead -> AAt _ _)      =  True
isFirstOrder (eraseToHead -> ATCon d _)    =  True
isFirstOrder (eraseToHead -> AAt _ _)      =  True
isFirstOrder (eraseToHead -> AType _)      = True
isFirstOrder _ = False
    
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
        simplUnboxBoxOnce (AUnboxVal (ABox a _)) = a
        simplUnboxBoxOnce a = a

-------------------------------------------------------
-- Dig through the context and get out all equations.
-------------------------------------------------------

-- Note, the returned value is already zonked
getAvailableEqs :: TcMonad [(ATerm, ATerm, ATerm)]
getAvailableEqs = do
  context <- getTys
  catMaybes <$> mapM (\(x,th,ty) -> do
                         zty <- zonkTerm ty
                         (th',a,ty') <- adjustTheta th (AVar x) zty
                         case eraseToHead ty' of
                           ATyEq tyLHS tyRHS -> return $ Just (a,tyLHS,tyRHS)
                           _ -> return $ Nothing)
                     context

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
-- The scrutinees and the branch-type are zonked before buildCase is called.
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
  ztyAlt <- zonkTerm tyAlt
  (ALet Runtime . bind (x, x_eq, embed s)) <$>
    (extendCtx (ASig x th sTy) $
      extendCtx (ASig x_eq Logic (ATyEq (AVar x) s)) $
        buildCase ((AVar x,y):scruts) alts ztyAlt)
buildCase ((s,y):scruts) alts tyAlt | not (null alts) && all isVarMatch alts = do
  --Todo: handle the scrutinee=pattern equation y somehow?
  alts' <- mapM (expandMatch s AEmpty <=< matchPat) alts
  buildCase scruts alts' tyAlt
buildCase ((s_unadjusted,y):scruts) alts tyAlt = do
  (th_unadjusted, sTy_unadjusted) <- aTs s_unadjusted
  (th,s,sTy) <- adjustTheta th_unadjusted s_unadjusted sTy_unadjusted
  (d, bbar, delta, cons) <- lookupDType s sTy
  let buildMatch :: AConstructorDef -> TcMonad AMatch
      buildMatch (AConstructorDef c args) = do
        relevantAlts <- filter (\(p,_) -> case p of 
                                           (PatCon (unembed -> c') _) -> (translate c')==c
                                           (PatVar _) -> True)
                           <$> mapM matchPat alts
        args' <- freshATele "_pat_" args --This may look silly, but we don't get it fresh for free.
        newScruts <- mapM (\x -> ((AVar (translate x)), ) <$> (fresh $ string2Name "_")) (binders args' :: [AName])
        let newScrutTys = simplSubsts (zip (binders delta) bbar) args'
        newAlts <- mapM (expandMatch s args') relevantAlts
        let erasedVars = aTeleErasedVars args'
                         `S.union` (S.singleton (translate y))
        ztyAlt <- zonkTerm tyAlt
        newBody <- extendCtxTele newScrutTys th $ 
                     extendCtx (ASig (translate y) Logic 
                                     (ATyEq s (ADCon c th bbar (aTeleAsArgs args')))) $
                       buildCase (newScruts++scruts) newAlts ztyAlt
        erasedNewBody <- erase newBody
        unless (S.null (S.map translate (fv erasedNewBody) `S.intersection` erasedVars)) $ do
          let (x:_) = S.toList (fv newBody `S.intersection` erasedVars)
          err [DS "The variable", DD x, DS "is marked erased and should not appear in the erasure of the case expression"]
        znewScrutTys <- zonkTele newScrutTys
        return $ AMatch c (bind znewScrutTys newBody)
  ematchs <- bind (translate y) <$> mapM buildMatch cons
  ztyAlt <- zonkTerm tyAlt
  return $ ACase s ematchs ztyAlt

-- | expandMatch scrut args (pat, alt) 
-- adjusts the ComplexMatch 'alt'
-- for the fact that 'scrut' has just been sucessfully tested against
-- pattern pat.  It adds the new variables args to the list of
-- patterns for alt, and substitutes scrut into the body of alt if
-- 'pat' was a variable pattern.a
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


------------- Some test code to exercise the annotated reduction semantics ----------

-- step the term until it's stuck.
reductionPath :: (a -> TcMonad (Maybe a)) -> a -> TcMonad [a]
reductionPath step a = do
  ma' <- step a
  case ma' of 
    Nothing -> return [a]
    Just a' ->  (a : ) <$> reductionPath step a'

newtype ReductionPath a = ReductionPath [a]

-- Printing reduction sequences
instance Disp a => Disp (ReductionPath a) where
  disp (ReductionPath ts) = foldr (\x y -> x $$ text "--->" $$ y) empty (map disp ts)

data AndTheErasureIs = AndTheErasureIs ATerm ETerm

instance Disp AndTheErasureIs where
  disp (a `AndTheErasureIs` t) = 
      disp a $$ parens (text "erased version:" $$ disp t)

testReduction :: ATerm -> TcMonad ()
testReduction a = do
  apath <- reductionPath astep a
  eLastA <- erase (last apath)
  eA <- erase a
  aEpath <- reductionPath cbvStep eA
  let lastEA = last aEpath
  apathAnn <- mapM ((return . uncurry AndTheErasureIs) <=< runKleisli (Kleisli return &&& Kleisli erase)) apath
  unless (eLastA `aeq` lastEA) $ do
    liftIO $ putStrLn "Oops, mismatch between annotated and erased semantics"
    liftIO $ putStrLn $ render (text "Erased reduction path:" $$ disp (ReductionPath aEpath))
    liftIO $ putStrLn $ render (text "Annotated reduction path:" $$ disp (ReductionPath apathAnn))
    err [DS "Something went wrong, see above"]

--Print the reductions
printReductionPath :: ATerm -> TcMonad ()
printReductionPath a = do
  liftIO $ putStrLn $ render (disp a)
  ma' <- astep a
  case ma' of 
    Nothing -> return ()
    Just a' -> do
                 liftIO $ putStrLn "---->"
                 printReductionPath a'
