{-# LANGUAGE ViewPatterns, TypeSynonymInstances, ExistentialQuantification, NamedFieldPuns, 
             ParallelListComp, FlexibleContexts, ScopedTypeVariables, TupleSections #-}
-- | The Trellys core typechecker, using a bi-directional typechecking algorithm
-- to reduce annotations.
module Language.Trellys.TypeCheck
  (tcModule,tcModules, runTcMonad, emptyEnv)
where

import Language.Trellys.Syntax

import Language.Trellys.PrettyPrint(Disp(..))
import Language.Trellys.OpSem

import Language.Trellys.Options
import Language.Trellys.Environment
import Language.Trellys.Error
import Language.Trellys.TypeMonad
import Language.Trellys.EqualityReasoning

import Language.Trellys.GenericBind
import Generics.RepLib.Lib(subtrees)
import Text.PrettyPrint.HughesPJ

import Control.Applicative ((<$>), (<*>))
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)
import Control.Arrow (first)

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S

{-
  We rely on two mutually recursive judgements:

  * ta is an analysis judgement that takes a term and a type and checks it

  * ts is a synthesis that takes a term and synthesizes a type

  Both functions also return an annotated term which is an
  elaborated version of the input term. The invariants for this is:
   - ta takes a source term and elaborated type, returns elaborated term
   - ts takes a source term, returns elaborated term and elaborated type.

  In both functions, we assume that the context (gamma) is an implicit argument,
 encapsulated in the TcMonad.
 -}


-- | kind check, for check = synthesis ?

-- Elaborate tm, and check that it is a well-formed type
-- at some level.
kcElab :: Theta -> Term -> TcMonad Term
kcElab th tm = do
  (etm,ty) <- ts th tm
  when (isNothing $ isType ty) $
    err [DD tm, DS "is not a well-formed type at", DD th]
  return etm

-- Check that tm is a wellformed type at some level
kc :: Theta -> Term -> TcMonad ()
kc th tm = void (kcElab th tm)

-- Apply kc to an entire telescope
kcTele :: Theta -> Telescope -> TcMonad ()
kcTele th [] = return ()
kcTele th ((x,ty,_):tele') = do
   kc th ty
   extendCtx (Sig x th ty) $  kcTele th tele'

-- | Type analysis
ta :: Theta -> Term -> Term -> TcMonad Term
-- Position terms wrap up an error handler
ta th (Pos p t) ty =
  extendSourceLocation p t $
    ta th t ty
ta th tm (Pos _ ty) = ta th tm ty

ta th (Paren a) ty = Paren <$> ta th a ty
ta th tm (Paren ty) = ta th tm ty
ta th tm (SubstitutedFor ty x) = ta th tm ty

-- rule T_join
ta th (Join s1 s2) (TyEq a b) =
  do kc th (TyEq a b)
     (ea,k1) <- ts Program a
     (eb,k2) <- ts Program b
     picky <- getFlag PickyEq
     when (picky && not (k1 `aeqSimple` k2)) $
         err [DS "Cannot join terms of different types:", DD a,
         DS "has type", DD k1, DS "and", DD b, DS "has type", DD k2]
     t1E <- erase =<< substDefs ea
     t2E <- erase =<< substDefs eb
     joinable <- join s1 s2 t1E t2E
     unless joinable $
       err [DS "The erasures of terms", DD a, DS "and", DD b,
            DS "are not joinable."]
     return (Join s1 s2)

    -- rule T_ord
ta _ (OrdAx a) (Smaller b1 b2) = do
     (ea,tyA) <- ts Logic a
     case isTyEq tyA of
       Just (a1, cvs) ->
         case cvs of 
           (Con _ vs) -> do
             unless (a1 `aeqSimple` b2) $
               err [DS "The left side of the equality supplied to ord ",
                    DS "should be", DD b2, 
                    DS "Here it is", DD a1]
             unless (any (\ (ai,_) -> ai `aeqSimple` b1) vs) $
                err [DS "The right side of the equality supplied to ord ",
                     DS "should be a constructor application involving", DD b1,
                     DS "Here it is", DD cvs]
             return (OrdAx ea)
           _ -> err [DS "The right side of the equality supplied to ord ",
                     DS "must be a constructor application.",
                     DS "Here it is", DD cvs]
       Nothing -> err [DS "The argument to ord must be an equality proof.",
                       DS "Here its type is", DD tyA]


-- rule T_contra
ta th (Contra a) b =
  do kc th b
     (ea, tyA) <- ts Logic a
     case isTyEq tyA of
       Just (cvs1, cvs2) ->
         case (cvs1, cvs2) of
           ((Con c1 vs1), (Con c2 vs2)) ->
              do when (c1 == c2) $
                   err [DS "The equality proof", DD tyA,
                        DS "isn't necessarily contradictory because the",
                        DS "constructors on both sides are the same."]
                 unless (   (all (isValue . fst) vs1)
                         && (all (isValue . fst) vs2)) $
                   err [DS "The equality proof", DD tyA,
                        DS "isn't necessarily contradictory because the",
                        DS "constructors are applied to non-values."]
                 return (Contra ea)
           _ -> err [DS "The equality proof supplied to contra must show",
                     DS "two different constructor forms are equal.",
                     DS "Here it shows", DD tyA]
       Nothing -> err [DS "The argument to contra must be an equality proof.",
                       DS "Here its type is", DD tyA]

-- rule T_abort
ta Logic Abort _ = err [DS "abort must be in P."]
ta Program Abort tyA = do kc Program tyA ; return Abort

-- Rules T_lam1 and T_lam2
ta th (Lam lep lbody) a@(Arrow aep abody) = do

  -- First check the arrow type for well-formedness
  kc th a

  -- pull apart the bindings and make sure the epsilons agree
  Just (x,body,(_,tyA),tyB) <- unbind2 lbody abody

  when (lep /= aep) $
       err ([DS "Lambda annotation", DD lep,
             DS "does not match arrow annotation", DD aep])

  -- typecheck the function body
  ebody <- extendCtx (Sig x th (unembed tyA)) (ta th body tyB)

  -- perform the FV and value checks if in T_Lam2
  bodyE <- erase ebody
  -- The free variables function fv is ad-hoc polymorphic in its
  -- return type, so we fix the type of xE.
  -- If we did (x `S.member` fv bodyE), fv would always return an empty set...
  let xE = translate x :: EName
  when (lep == Erased && xE `S.member` fv bodyE) $
       err [DS "ta: In implicit lambda, variable", DD x,
            DS "appears free in body", DD body]

  when (th == Program && lep == Erased) $ do
    unless (isValue body) $
        err [DS "ta : The body of an implicit lambda must be a value",
             DS "but here is:", DD body]

  return (Lam lep (bind x ebody))

-- rules T_ind1 and T_ind2
ta _ (Ind ep binding) arr@(Arrow aep abnd) = do
  kc Logic arr

  unless (ep == aep) $
     err [DS "ta : expecting argument of ind to be", DD aep,
          DS "got", DD ep]

  ((dumbvar,tyA),dumbbody) <- unbind abnd

  ((f,y),a) <- unbind binding
  -- to get the body "tyB" as it appears on paper, we must replace the
  -- extra variable we got from opening the binding
  let tyB = subst dumbvar (Var y) dumbbody
  

  -- next we must construct the type C.  we need new variables for x and z
  x <- fresh (string2Name "x")
  z <- fresh (string2Name "z")
  let xTyB = subst y (Var x) tyB
      smallerType = Smaller (Var x)
                            (Var y)

      tyC = Arrow ep (bind (x, tyA) --Is this right or do we need, like (embed(unembedd tyA))?
                  (Arrow Erased (bind (z,embed smallerType)
                         xTyB)))
  -- Finally we can typecheck the fuction body in an extended environment
  ea <- extendCtx (Sig f Logic tyC) $
          extendCtx (Sig y Logic (unembed tyA)) $ ta Logic a tyB
  -- in the case where ep is Erased, we have the two extra checks:
  aE <- erase ea
  when (ep == Erased && translate y `S.member` fv aE) $
       err [DS "ta: In implicit ind, variable", DD y,
            DS "appears free in body", DD a]

  when (ep == Erased) $ do
       unless (isValue a) $
              err [DS "The body of an implicit ind must be a value",
                   DS "but here is:", DD a]
  return (Ind ep (bind (f,y) ea))


-- rules T_rec1 and T_rec2
ta Logic (Rec _ _) _ =
  err [DS "rec must be P."]

ta Program (Rec ep binding) fty@(Arrow aep abnd) = do
  kc Program fty
  unless (ep == aep) $
         err [DS "ta : expecting argument of rec to be",
              DD aep, DS ", got", DD ep]

  ((dumby,tyA),dumbbody) <- unbind abnd
  ((f,y),a) <- unbind binding
  let tyB = subst dumby (Var y) dumbbody

  ea <- extendCtx (Sig f Program fty) $
          extendCtx (Sig y Program (unembed tyA)) $
            ta Program a tyB

  -- perform the FV and value checks if in T_RecImp
  aE <- erase ea
  when (ep == Erased && translate y `S.member` fv aE) $
       err [DS "ta: In implicit rec, variable", DD y,
            DS "appears free in body", DD a]
  when (ep == Erased) $ do
    unless (isValue a) $
       err [DS "ta : The body of an implicit rec must be a value",
            DS "but here is:", DD a]
  return (Rec ep (bind (f,y) ea))

-- rule T_case
ta th (Case b bnd) tyA = do
  -- premises 1, 3 and 4: we check that the scrutinee is the element of some
  -- datatype defined in the context
  (eb,bty) <- ts th b
  (d,bbar,delta,cons) <- lookupDType th b bty

  -- premise 2: the return type must be well kinded
  kc th tyA
  (y,mtchs) <- unbind bnd

  -- premises 4 and 5: we define a function to map over the
  -- branches that checks each is OK (and elaborates it)
  unless (length mtchs == length cons) $
    err [DS "Wrong number of pattern match branches for datatype", DD d]
  let taMatch :: Match -> TcMonad Match
      taMatch (Match c cbnd) = do
        dumbdeltai <- lookupDCon d c
        (deltai',ai) <- unbind cbnd
        unless (length deltai' == length dumbdeltai) $
          err [DS "wrong number of argument variables for constructor",
               DD c, DS "in pattern match."]
        unless (   (map snd deltai')
                == map (\(_,_,e) -> e) dumbdeltai) $
           err [DS "wrong epsilons on argument variables for constructor",
                DD c, DS "in pattern match."]
        let deltai = swapTeleVars dumbdeltai (map fst deltai')
            subdeltai = substs (zip (domTele delta) (map fst bbar)) deltai
            eqtype = TyEq b (Con c (bbar ++ map (\(x,_,ep) -> (Var x, ep)) deltai))
         -- premise 5
        eai <- extendCtx (Sig y Logic eqtype) $
                           extendCtxTele subdeltai th $ ta th ai tyA
        -- premise 6
        aE <- erase eai
        let yEs = map translate $ y : domTeleMinus deltai
        let shouldBeNull = S.fromList yEs `S.intersection` fv aE
        unless (S.null shouldBeNull) $
          err [DS "The constructor argument(s) and/or scrutinee equality proof",
               DD . S.toList $ shouldBeNull,
               DS "should not appear in the erasure", DD aE,
               DS "of the term", DD ai,
               DS "because they bind compiletime variables."]
        return $ Match c (bind deltai' eai)         
  emtchs <- mapM taMatch mtchs
  return (Case eb (bind y emtchs))

ta th (ComplexCase bnd) tyB = do
   isElaborating <- getFlag Elaborate
   unless isElaborating $
     err [DS "Trying to elaborate a complex case statement when not in elaboration mode."]
   (scruts, alts) <- unbind bnd
   let checkNumPats (ComplexMatch bnd1) = do
         (pats, body) <- unbind bnd1
         unless (length pats == length scruts) $
           err [ DS $"Each branch should have " ++ show (length scruts) ++ " patterns, but",
                 DD (ComplexMatch bnd1), DS $ "has " ++ show (length pats) ++  "."]
   mapM_ checkNumPats alts
   scrutTys <- mapM (fmap snd . ts th . unembed . fst) scruts
   b <- buildCase th scruts scrutTys alts
   ta th b tyB

-- implements the checking version of T_let1 and T_let2
ta th (Let th' ep bnd) tyB =
 do -- begin by checking syntactic -/L requirement and unpacking binding
    when (ep == Erased && th' == Program) $
       err [DS "Implicit lets must bind logical terms."]
    ((x,y,a),b) <- unbind bnd
    -- premise 1
    (ea,tyA) <- ts th' (unembed a)
    -- premise 2
    eb <- extendCtx (Sig y Logic (TyEq (Var x) ea)) $
            extendCtx (Sig x th' tyA) $
              ta th b tyB
    -- premise 3
    kc th tyB
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
    unless (th' <= th) $
      err [DS "Program variables can't be bound with let expressions in",
           DS "Logical contexts because they would be normalized when the",
           DS "expression is."]
    return (Let th' ep (bind (x,y,embed ea) eb))
-- rule T_At
ta _ (At ty th') (Type i) = do 
   ea <- ta th' ty (Type i)
   return (At ea th')
-- rule T_AtP
ta Program a (At tyA th) = ta th a tyA
-- rule T_AtLL
ta Logic a (At tyA Logic) = ta Logic a tyA
-- rule T_AtLP
ta Logic a (At tyA Program) = 
   -- allow a to be "provable value here..."
   if (isValue a) then 
      ta Program a tyA
   else 
      -- one last chance, check if it is a log term immediately 
      -- coerced to be programmatic
      ta Logic a tyA    
   
ta th (TerminationCase s binding) ty = do 
    (es, sty) <- ts Program s
    (w,(abort,tbind)) <- unbind binding
    (v, terminates) <- unbind tbind
    eabort <- extendCtx (Sig w Logic (TyEq (Ann Abort sty) s))
                 $ ta th abort ty
    eterm  <- extendCtx (Sig v Program sty)
                 $ extendCtx (Sig w Logic (TyEq (Var v) s))
                 $ ta th terminates ty
    return (TerminationCase es (bind w (eabort, (bind v eterm))))

ta th TrustMe ty = return TrustMe

ta th InferMe (TyEq ty1 ty2) = do
  isElaborating <- getFlag Elaborate
  unless isElaborating $
    err [DS "Trying to typecheck an InferMe when not in elabortion mode"]
  context <- getTys
  let availableEqs = catMaybes $ map (\(x,th,ty) -> do guard (th==Logic)
                                                       (ty1,ty2) <- isTyEq ty
                                                       Just (x,ty1,ty2))
                                      context
--  warn [DS "About to try to prove:",  DD (Goal (map (\(x,ty1,ty2) -> Sig x Logic (TyEq ty1 ty2)) availableEqs) 
--                                                 (TyEq ty1 ty2))]
  pf <- prove availableEqs (ty1,ty2)
  case pf of
    Nothing ->
      err [DS "I was unable to prove:", DD (Goal (map (\(x,ty1,ty2) -> Sig x Logic (TyEq ty1 ty2)) availableEqs) 
                                                 (TyEq ty1 ty2))]
    Just p -> return p

ta th InferMe ty  = err [DS "I only know how to prove equalities, this goal has type", DD ty]

-- pass through SubstitutedFor
ta th (SubstitutedFor a x) tyA = do
  ea <- ta th a tyA
  return (SubstitutedFor ea x)

-- rule T_chk
ta th a tyB = do
  (ea,tyA) <- ts th a
  isSubtype <- subtype th tyA tyB
  if isSubtype
    then return ea
    else do 
      isElaborating <- getFlag Elaborate
      if isElaborating
       then do
         context <- getTys
         let availableEqs = catMaybes $ map (\(x,th,ty) -> do guard (th==Logic)
                                                              (ty1,ty2) <- isTyEq ty
                                                              Just (x,ty1,ty2))
                                            context
--         warn [DS "About to try to prove:",  DD (Goal (map (\(x,ty1,ty2) -> Sig x Logic (TyEq ty1 ty2)) availableEqs) 
--                                                 (TyEq tyA tyB))]
         pf <- prove availableEqs (tyA,tyB)
         case pf of 
           Nothing ->
             err [DS "When checking term", DD a, DS "against type",
                  DD tyB, DS "the distinct type", DD tyA,
                  DS "was inferred instead.",
                  DS "I was unable to prove:", DD (Goal (map (\(x,ty1,ty2) -> Sig x Logic (TyEq ty1 ty2)) availableEqs) 
                                                  (TyEq tyA tyB))]
           Just p -> do
                       x <- fresh (string2Name "x")
                       return $ Conv ea [(p,Runtime)] (bind [x] (Var x))         
       else err [DS "When checking term", DD a, DS "against type",
                 DD tyB, DS "the distinct type", DD tyA,
                 DS "was inferred instead.",
                 DS "(Not in elaboration mode, so no automatic coersion was attempted.)"]


-- | Checks a list of terms against a telescope of types
-- Returns list of elaborated terms.
-- Precondition: the two lists have the same length.
taTele :: Theta -> [(Term,Epsilon)] -> Telescope -> TcMonad [(Term,Epsilon)]
taTele th [] [] = return []
taTele th ((t,ep1):ts) ((x,ty,ep2):tele')  = do
  unless (ep1 == ep2) $
    err [DS "The term ", DD t, DS "is", DD ep1, DS "but should be", DD ep2]
  et <- ta th t ty
  ets <- taTele th ts (subst x t tele')
  return $ (et,ep1) : ets
taTele _ _ _ = error "Internal error: taTele called with unequal-length arguments"    


------------------------------
------------------------------
-------- Synthesis
------------------------------
------------------------------

-- | type synthesis
-- Returns (elaborated term, type of term)
ts :: Theta -> Term -> TcMonad (Term,Term)
ts tsTh tsTm =
  do (etsTm, typ) <- ts' tsTh tsTm
     return $ (etsTm, delPosParenDeep typ)
  where
    ts' :: Theta -> Term -> TcMonad (Term,Term)
    ts' th (Pos p t) =
      extendSourceLocation p t $       
        ts' th t

    ts' th (Paren a) =
      do (ea,ty) <- ts' th a
         return (Paren ea, ty)

    -- Rule T_var/T_unboxVar
    {- Variables are a bit special, because both the intro and elimination rules for @ always apply.
       So without loss of generality we can "eagerly" apply unbox to the type we looked up from the
       context. Another way to look at it is to say that we synthesize both the type and the th
       for the variable, unlike the other synthesis rules that take th as an input. Finally, if the th
       we got was not the one we were asked for, we apply either t_fo, or box.
    -}
    ts' th (Var y) =
      do x <- lookupTy y
         case x of
           Just (th',ty) -> do
             let (th0', ty0) = stripAts th ty  --Repeatedly use T_unboxVar
             isFO <- isFirstOrder ty0
             if (th0' <= th) --the th we found is good enough
              then return (Var y, ty0)
              else if isFO -- (implicitly) apply T_FO
                then return (Var y, ty0)
                else -- (implicity) apply T_box
                  return (Var y, At ty0 th0')
           Nothing -> err [DS "The variable", DD y, DS "was not found."]
     where stripAts :: Theta -> Term -> (Theta, Term)
           stripAts th ty = case isAt ty of
                              Just (ty', th') -> stripAts th' ty'
                              _ -> (th, ty)       

    -- Rule T_type
    ts' _ (Type l) = return (Type l,  Type (l + 1))

    -- Rules T_pi and T_pi_impred
    ts' th (Arrow ep body) =
      do ((x,tyA), tyB) <- unbind body
         isFO <- isFirstOrder (unembed tyA)
         unless isFO $
           err [DD (unembed tyA), 
                DS  "can not be used as the domain of a function type, must specify either",
                DD (At (unembed tyA) Logic), DS "or", DD (At (unembed tyA) Program)]
         (etyA, tytyA) <- ts th (unembed tyA)
         (etyB, tytyB) <- extendCtx (Sig x th (unembed tyA)) $ ts th tyB
         case (isType tytyA, isType tytyB) of
           (Just _, Just 0) -> return $ (Arrow ep  (bind (x,embed etyA) etyB), Type 0)
           (Just n, Just m) -> return $ (Arrow  ep  (bind (x,embed etyA) etyB), Type (max n m))
           (Just _, _)      -> err [DD tyB, DS "is not a type."]
           (_,_)            -> err [DD (unembed tyA), DS "is not a type.", DS "inferred", DD tytyA, DS "at", DD th]

    -- Rules T_tcon, T_acon and T_dcon
    ts' th (Con c args) =
      do typC <- lookupCon c
         case typC of
           (Left (delta, th', lev, _)) ->
             do unless (th' <= th) $
                  err [DS "Datatype constructor", DD c,
                       DS "is programmatic, but it was checked logically."]
                unless (length args == length delta) $
                  err [DS "Datatype constructor", DD c, 
                       DS $ "should have " ++ show (length delta) ++
                       "parameters, but was given", DD (length args)]
                eargs <- taTele th args delta
                return (Con c eargs, (Type lev))
           (Right (tname, delta, th', ConstructorDef _ _ deltai)) ->
             do unless (th' <= th) $
                  err [DS "Data constructor", DD c,
                       DS "is programmatic, but it was checked logically."]
                unless (length args == length delta + length deltai) $
                  err [DS "Constructor", DD c,
                       DS $ "should have " ++ show (length delta) ++ " parameters and " ++ show (length deltai)
                       ++ " data arguments, but was given " ++ show (length args) ++ " arguments."]
                eargs <- taTele th args (setTeleEps Erased delta ++ deltai)
                let eindices = map (\(t,_)->(t,Runtime)) (take (length delta) eargs)
                return $ (Con c eargs, Con tname eindices)

    -- rule T_app
    ts' th tm@(App ep a b) =
      do (ea,tyArr) <- ts th a
         case isArrow tyArr of
           Nothing -> err [DS "ts: expected arrow type, for term ", DD a,
                           DS ". Instead, got", DD tyArr]
           Just (epArr, bnd) -> do
             ((x,tyA),tyB) <- unbind bnd
             unless (ep == epArr) $
               err [DS "Application annotation", DD ep, DS "in", DD tm,
                    DS "doesn't match arrow annotation", DD epArr]

             let b_for_x_in_B = subst x b tyB
             -- check that the result kind is well-formed
             kc th b_for_x_in_B
             -- check the argument, at the "A" type
             eb <- ta th b (unembed tyA)
             return (App ep ea eb, b_for_x_in_B)

    -- rule T_smaller
    ts' _ (Smaller a b) = do
      (ea,_) <- ts Program a
      (eb,_) <- ts Program b
      return $ (Smaller ea eb, Type 0)

    -- rule T_ordtrans
    ts' _ (OrdTrans a b) = do
      (ea,tyA) <- ts Logic a
      (eb,tyB) <- ts Logic b
      case (isSmaller tyA, isSmaller tyB) of 
        (Just (a1,a2), Just (b1,b2)) -> do
          unless (a2 `aeqSimple` b1) $
            err [DS "The middle terms of the inequalities given to ordtrans must match, ",
                 DS "but here they are", DD a2, DS "and", DD b1]
          return $ (OrdTrans ea eb, Smaller a1 b2)
        (Nothing, _) -> err [DS "The arguments to ordtrans must be proofs of <, ",
                             DS "but here the first argument has type", DD tyA]
        (_, Nothing) -> err [DS "The arguments to ordtrans must be proofs of <, ",
                             DS "but here the second argument has type", DD tyB]

    -- rule T_eq
    ts' _ (TyEq a b) = do
      (ea,_) <- ts Program a
      (eb,_) <- ts Program b
      return $ (TyEq ea eb, Type 0)

    -- rule T_conv
    ts' th (Conv b as bnd) =
      do (xs,c) <- unbind bnd
         let chkTy (pf,Runtime) = do
               (epf,t) <- ts Logic pf
               return ((epf,Runtime),t)
             chkTy (pf,Erased) = do
               return ((pf,Erased),pf) --fixme: pf should be elaborated, but that needs the context from the template...
         (eas,atys) <- unzip <$> mapM chkTy as

         picky <- getFlag PickyEq

         (tyA1s,tyA2s, ks) <- unzip3 <$> mapM (\ aty ->
              case isTyEq aty of
                Just (tyA1, tyA2) -> do
                 (_,k1) <- ts Program tyA1
                 (_,k2) <- ts Program tyA2
                 when (picky && (not (k1 `aeqSimple` k2))) $ err
                   [DS "Terms ", DD tyA1, DS "and", DD tyA2,
                    DS " must have the same type when used in conversion.",
                    DS "Here they have types: ", DD k1, DS "and", DD k2,
                    DS "respectively."]

                 return (tyA1, tyA2, k1)
                _ -> err $ [DS "The second arguments to conv must be equality proofs,",
                            DS "but here has type", DD aty]

              ) atys

         -- One annoying twist is that we need to elaborate the pattern c also,
         -- or else surface-language stuff will leak through into the elaborated program.
         -- I wonder if there is a better way of doing this...

         let cA1 = substs (zip xs (zipWith SubstitutedFor tyA1s xs)) c
         let cA2 = substs (zip xs (zipWith SubstitutedFor tyA2s xs)) c
         eb <- ta th b cA1
         ecS <- if picky then
                  -- check c with extended environment
                  -- Don't know whether these should be logical or programmatic
                  let decls = zipWith (\ x t -> Sig x Logic t) xs ks in
                    extendCtxs decls $ kcElab th c
                else
                  -- check c after substitution
                  kcElab th cA2
         let ec = unsubstitute ecS

         erasedEc <- erase ec
         let chkErased (pf,Runtime) _ = return ()
             chkErased (pf,Erased) var = do
               when (translate var `S.member` fv erasedEc) $
                   err [DS "Equality proof", DD pf, DS "is marked erased",
                        DS "but the corresponding variable", DD var,
                        DS "appears free in the erased term", DD erasedEc]
         zipWithM_ chkErased as xs

         return (Conv eb eas (bind xs ec), ecS)

    -- rule T_annot
    ts' th (Ann a tyA) =
      do etyA <- kcElab th tyA
         ea <- ta th a etyA
         return (Ann ea etyA, etyA)

    -- pass through SubstitutedFor
    ts' th (SubstitutedFor a x) =
     do (ea,tyA) <- ts' th a
        return (SubstitutedFor ea x, tyA)

    -- the synthesis version of rules T_let1 and T_let2
    ts' th (Let th' ep bnd) =
     do -- begin by checking syntactic -/L requirement and unpacking binding
        when (ep == Erased && th' == Program) $
          err [DS "Implicit lets must bind logical terms."]
        ((x,y,a),b) <- unbind bnd
        -- premise 1
        (ea,tyA) <- ts th' (unembed a)
        -- premise 2
        (eb,tyB) <- extendCtx (Sig y Logic (TyEq (Var x) ea)) $
                      extendCtx (Sig x th' tyA) $
                        ts th b
        -- premise 3
        kc th tyB
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
        unless (th' <= th) $
          err [DS "Program variables can't be bound with let expressions in",
               DS "Logical contexts because they would be normalized when the",
               DS "expression is."]
        return (Let th' ep (bind (x,y,embed ea) eb), tyB)

    -- T_at
    ts' _ (At tyA th') = do
      (ea, s) <- ts th' tyA
      return (At ea th', s)

    ts' _ tm = err $ [DS "Sorry, I can't infer a type for:", DD tm,
                      DS "Please add an annotation.",
                      DS "NB: This error happens when you misspell,",
                      DS "so check your spelling if you think you did annotate."]


--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------


-- | Typecheck a collection of modules. Assumes that each modules
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked and elaborated into the core
-- language.
tcModules :: [Module] -> TcMonad [Module]
tcModules mods = foldM tcM [] mods
  -- Check module m against modules in defs, then add m to the list.
  where defs `tcM` m = do -- "M" is for "Module" not "monad"
          let name = moduleName m
          liftIO $ putStrLn $ "Checking module " ++ show name
          m' <- defs `tcModule` m
          return $ defs++[m']

-- | Typecheck an entire module.
tcModule :: [Module] -- ^ List of already checked modules (including their Decls).
         -> Module           -- ^ Module to check.
         -> TcMonad Module   -- ^ The same module with all Decls checked and elaborated.
tcModule defs m' = do checkedEntries <- extendCtxMods importedModules $
                                          foldr tcE (return [])
                                                  (moduleEntries m')
                      return m'{ moduleEntries = checkedEntries }
  where d `tcE` m = do
          -- Extend the Env per the current Decl before checking
          -- subsequent Decls.
          x <- tcEntry d
          case x of
            AddHint  hint  -> extendHints hint m
                           -- Add decls to the Decls to be returned
            AddCtx decls -> (decls++) <$> (extendCtxs decls m)
        -- Get all of the defs from imported modules (this is the env to check current module in)
        importedModules = filter (\aMod -> (ModuleImport (moduleName aMod)) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Decl.
data HintOrCtx = AddHint Decl
               | AddCtx [Decl]
                 -- Q: why [Decl] and not Decl ? A: when checking a
                 -- Def w/o a Sig, a Sig is synthesized and both the
                 -- Def and the Sig are returned.

tcEntry :: Decl -> TcMonad HintOrCtx

tcEntry (Def n term) = do
  oldDef <- lookupDef n
  case oldDef of
    Nothing -> tc
    Just term' -> die term'
  where
    tc = do
      lkup <- lookupHint n
      case lkup of
        Nothing -> do (eterm,ty) <- ts Logic term
                      -- Put the elaborated version of term into the context.
                      return $ AddCtx [Sig n Logic ty, Def n eterm]
        Just (theta,ty) ->
          let handler (Err ps msg) = throwError $ Err (ps) (msg $$ msg')
              msg' = disp [DS "When checking the term ", DD term,
                           DS "against the signature", DD ty]
          in do
            eterm <- ta theta term ty `catchError` handler
            -- If we already have a type in the environment, due to a sig
            -- declaration, then we don't add a new signature.
            --
            -- Put the elaborated version of term into the context.
            return $ AddCtx [Sig n theta ty, Def n eterm]
    die term' =
      extendSourceLocation (unPosFlaky term) term $
         err [DS "Multiple definitions of", DD n,
              DS "Previous definition at", DD (unPosFlaky term'),
              DS " was", DD term']

-- rule Decl_data
tcEntry dt@(Data t delta th lev cs) =
  do -- The parameters of a datatype must all be Runtime.
     unless (all (\(_,_,ep) -> ep==Runtime) delta) $
       err [DS "All parameters to a datatype must be marked as relevant."]
     ---- Premise 1
     kc th (telePi delta (Type lev))  
     ---- Premise 2: check that the telescope provided 
     ---  for each data constructor is wellfomed.
     ---  fixme: probably need to worry about universe levels also?
     extendCtx (AbsData t delta th lev) $
        mapM_ (\d@(ConstructorDef pos _ tele) -> extendSourceLocation pos d $ kcTele th (delta++tele)) cs
     -- Premise 3: check that types are strictly positive.
     when (th == Logic) $
       mapM_ (positivityCheck t) cs
     -- Implicitly, we expect the constructors to actually be different...
     unless (length cnames == length (nub cnames)) $
       err [DS "Datatype definition", DD t, DS"contains duplicated constructors" ]
     -- finally, add the datatype to the env and perform action m
     -- fixme, we should really add an elaborated version of the declaration.
     return $ AddCtx [dt]
     where cnames = map (\(ConstructorDef _ c _) -> c) cs

tcEntry dt@(AbsData _ delta th lev) =
  do kc th (telePi delta (Type lev))
     return $ AddCtx [dt]

tcEntry (Sig n th ty) = do
  duplicateTypeBindingCheck n ty
  ety <- kcElab th ty
  return $ AddHint (Sig n th ety)

tcEntry (Axiom n th ty) = do
  duplicateTypeBindingCheck n ty
  ety <- kcElab th ty
  return $ AddCtx [Axiom n th ety]

duplicateTypeBindingCheck :: TName -> Term -> TcMonad ()
duplicateTypeBindingCheck n ty = do
  -- Look for existing type bindings ...
  l  <- lookupTy n
  l' <- lookupHint n
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

-----------------------
------ subtyping
-----------------------
subtype :: Theta -> Term -> Term -> TcMonad Bool
subtype Program (Type _) (Type _) = return True
subtype Logic (Type l1) (Type l2) = return (l1 <= l2)
subtype _ a b = return $ (delPosParenDeep a) `aeq` (delPosParenDeep b)


isFirstOrder :: Term -> TcMonad Bool
isFirstOrder ty = isFirstOrder' S.empty ty
  where
    isFirstOrder' :: Set TName -> Term -> TcMonad Bool
    isFirstOrder' _ (TyEq _ _) = return True
    isFirstOrder' _ (Smaller _ _) = return True
    isFirstOrder' s (Pos _ ty) = isFirstOrder' s ty
    isFirstOrder' s (Paren ty) = isFirstOrder' s ty
    isFirstOrder' s (Con d _) | d `S.member` s = return True
    isFirstOrder' s (Con d _) = do
      ent <- lookupCon d
      case ent of
        (Left (_,_,_,Nothing))  -> 
          --An abstract datatype constructor. Maybe this is too conservative?
          return False
        (Left (_,_,_,Just cons)) ->
          -- Datatypes are FO if all components are. But in order to not get caught in an
          -- infinite loop, we should probably give the constructor d the "benefit of the
          -- doubt"  while doing so...
          allM (\(ConstructorDef _ _ args) -> allM (\(_,ty,_) -> isFirstOrder' (S.insert d s) ty) args) cons 
        (Right _) -> 
          -- Data constructors are never first-order.
          return False
    isFirstOrder' _ (At _ _) = return True
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


-- Alpha equality, dropping parens and source positions.

aeqSimple :: Alpha t => t -> t -> Bool
aeqSimple x y = delPosParenDeep x `aeq` delPosParenDeep y


---------------------------------------------------------------------------
-- Looking up datatypes in the context, when typechecking case-expressions.
---------------------------------------------------------------------------

-- | If ty is a datatype, then return its definition, otherwise signal an error.

--  (d,bbar,delta,cons) <- lookupDType bty

lookupDType :: Theta -> Term -> Term -> TcMonad (TName, [(Term, Epsilon)], Telescope, [ConstructorDef])
lookupDType th b bty@(isCon -> Just (d, apps)) = do
         ent <- lookupCon d
         case ent of
           (Left (delta,th',_,Just cons)) ->
             do unless (th' <= th) $
                   err [DS "Attempted to pattern match on an element of the",
                        DS "datatype", DD d, DS "in the Logical fragment, but",
                        DS "it is programmatic."]
                unless (length apps == length delta) $
                   err [DS "Attempted to match against", DD b,
                        DS "with type", DD bty, DS "where", DD d,
                        DS "is applied to the wrong number of arguments."]
                return (d,map (\(a,_) -> (a,Erased)) apps, delta, cons)
           (Left (_,_,_,Nothing)) ->
              err [DS "Scrutinee ", DD b,
                   DS "is a member of an abstract datatype - you may not",
                   DS "pattern match on it."]
           _ ->
              err [DS "Scrutinee ", DD b,
                   DS "must be a member of a datatype, but is not. It has type", DD bty]
lookupDType _ b bty = err [DS "Scrutinee ", DD b,
                           DS "must be a member of a datatype, but is not. It has type", DD bty]

-- | (lookupDCon d c) finds the arguments of constructor c, which should be one of the constructors of d.
lookupDCon :: TName -> TName -> TcMonad Telescope
lookupDCon d c = do
  dDef <- lookupCon d
  case dDef of 
    (Left (_,_,_,Just cons)) -> 
       case find (\(ConstructorDef  _ c' _) -> c'==c) cons of
         Nothing -> err [DD c, DS "is not a constructor of type", DD d]
         Just (ConstructorDef _  _ deltai)  -> return deltai
    _ -> err [DD c, DS "is not a constructor of type", DD d]

---------------------------------------
-- Some random utility functions
---------------------------------------

allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM p = liftM and . mapM p

freshTele :: (Functor m, Fresh m) => Telescope -> m Telescope
freshTele = mapM (\(x,ty,ep) -> (,ty,ep) <$> fresh x)

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

-- (buildCase th scrutinees scrutineeTys alts) builds a case tree that
-- evaluates to the first alternative that matches, or 'fallback' if
-- none of them do. The argument scrutineeTys is a list of the types of the scrutinees.
--
-- precondition: scrutineeTys has the same length as scrutinees, and all the pattern lists have the same length 
-- as scrutinees.
buildCase ::Theta ->  [(Embed Term, TName)] -> [Term] -> [ComplexMatch] -> TcMonad Term
buildCase _  [] _ [] = err [DS "Patterns in caes-expression not exhaustive."]
buildCase _  [] _ (alt:_) = matchBody alt
buildCase th ((unembed->s,y):scruts) (ty:scrutTys) alts | not (null alts) && all isVarMatch alts = do
  alts' <- mapM (expandMatch th s [] <=< matchPat) alts
  buildCase th scruts scrutTys alts'
buildCase th ((unembed->s,y):scruts) (sTy:scrutTys) alts = do
  (d, bbar, delta, cons) <- lookupDType th s sTy
  let buildMatch :: ConstructorDef -> TcMonad Match
      buildMatch (ConstructorDef _ c args) = do
        args <- freshTele args --This may look silly, but we don't get it fresh for free.
        relevantAlts <- filter (\(p,_) -> case p of 
                                           (PatCon (unembed -> c') _) -> c'==c
                                           (PatVar _) -> True)
                           <$> mapM matchPat alts
        newScruts <- mapM (\(x,_,_) -> (embed (Var x), ) <$> (fresh $ string2Name "_")) args
        let newScrutTys = map (\(_,ty,_) -> ty) $ substs (zip (domTele delta) (map fst bbar)) args
        newAlts <- mapM (expandMatch th s args) relevantAlts
        Match c <$> (bind (map (\(x,_,ep) -> (x,ep)) args) 
                      <$> buildCase th (newScruts++scruts) (newScrutTys++scrutTys) newAlts)
  Case s <$> (bind y <$> mapM buildMatch cons)

-- | expandMatch th scrut args (pat, alt) 
-- adjusts the ComplexMatch 'alt' for the fact that 'scrut' (which belongs to the 'th' sublanguage)
-- has just been sucessfully tested against pattern pat.
-- It adds the new variables args to the list of patterns for alt, and substitutes scrut into the body of alt 
-- if 'pat' was a variable pattern.
expandMatch :: Theta -> Term -> Telescope -> (Pattern, ComplexMatch) -> TcMonad ComplexMatch
expandMatch th s args (PatCon (unembed -> c) newPats, ComplexMatch alt) = do
  unless (length newPats == length args) $ 
    err [DS "constructor", DD c, DS $ "should take " ++ show (length args) ++ " constructors,",
         DS "but the pattern", DD (PatCon (embed c) newPats), DS $ "has " ++ show (length newPats) ++ "."]
  unless (map (\(_,_,ep)->ep) args == map snd newPats) $
    err [DS "wrong epsilons on arguments in pattern", DD (PatCon (embed c) newPats)]
  (pats, body) <- unbind alt
  return $ ComplexMatch (bind (map fst newPats++pats) body)
expandMatch th s args (PatVar z, ComplexMatch alt) = do
  newPats <- mapM (\(_,_,ep) -> do x <- fresh (string2Name  "_"); return (PatVar x, ep)) args
  (pats, body) <- unbind alt
  case isVar s of 
    Just x -> return $ ComplexMatch (bind (map fst newPats++pats) (subst z (Var x) body))
    Nothing -> do
      x    <- fresh (string2Name "x")
      x_eq <- fresh (string2Name "x_eq")
      return $ ComplexMatch (bind (map fst newPats++pats)
                                  (Let th Runtime (bind (x, x_eq, embed s) 
                                                        (subst z (Var x) body))))

isVarMatch :: ComplexMatch -> Bool
isVarMatch (ComplexMatch bnd) = 
 --unsafeUnbind is ok since we never look at the names, only the top constructor.
 let (pats, _) = unsafeUnbind bnd in
 case pats of
   (PatVar _ : _) -> True
   _ -> False

matchBody :: (Functor m, Fresh m) => ComplexMatch -> m Term
matchBody (ComplexMatch bnd) = snd <$> unbind bnd

-- Precondition: the match has at least one pattern.
matchPat :: (Functor m, Fresh m) => ComplexMatch -> m (Pattern, ComplexMatch)
matchPat (ComplexMatch bnd) = do
  ((pat:pats), body) <- unbind bnd
  return (pat, ComplexMatch $ bind pats body)
