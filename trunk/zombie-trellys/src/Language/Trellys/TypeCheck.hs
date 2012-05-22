{-# LANGUAGE TypeSynonymInstances, ExistentialQuantification, NamedFieldPuns, ParallelListComp, FlexibleContexts, ScopedTypeVariables #-}
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

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S

-- import System.IO.Unsafe (unsafePerformIO)

{-
  We rely on two mutually recursive judgements:

  * ta is an analysis judgement that takes a term and a type and checks it

  * ts is a synthesis that takes a term and synthesizes a type

  Both functions also return an annotated term which is a (possibly)
  elaborated version of the input term.

  In both functions, we assume that the context (gamma) is an implicit argument,
encapsulated in the TcMonad.

 -}


-- | kind check, for check = synthesis ?

-- Check that tm is a wellformed type at some level
kc :: Theta -> Term -> TcMonad ()
kc th tm = do
  (_,ty) <- ts th tm
  when (isNothing $ isType ty) $
    err [DD tm, DS "is not a well-formed type at", DD th]
--         ,DS "it should have type Type but has type", DD ty]

-- Apply kc to an entire telescope
kcTele :: Theta -> Telescope -> TcMonad ()
kcTele th [] = return ()
kcTele th ((x,ty,_):tele') = do
   kc th ty
   extendCtx (Sig x th ty) $  kcTele th tele'

-- | Type analysis
ta :: Theta -> Term -> Term -> TcMonad Term
-- Position terms wrap up an error handler
ta th (Pos p t) ty = do
  extendSourceLocation p t $
    ta th t ty
ta th tm (Pos _ ty) = ta th tm ty

ta th (Paren a) ty = Paren <$> ta th a ty
ta th tm (Paren ty) = ta th tm ty

-- rule T_join
ta th (Join s1 s2) (TyEq a b) =
  do kc th (TyEq a b)
     (_,k1) <- ts Program a
     (_,k2) <- ts Program b
     picky <- getFlag PickyEq
     when (picky && not (k1 `aeqSimple` k2)) $
         err [DS "Cannot join terms of different types:", DD a,
         DS "has type", DD k1, DS "and", DD b, DS "has type", DD k2]
     t1E <- erase =<< substDefs a  --fixme, maybe we should actually compare elaborated types?
     t2E <- erase =<< substDefs b
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
  -- SCW: can relax and check this at P even with th is v if b is "valuable"
  (eb,bty) <- ts th b
  (d,bbar,delta,cons) <-
    case bty of
      (Con d apps) -> do
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
      _ -> err [DS "Scrutinee ", DD b,
                DS "must be a member of a datatype, but is not. It has type", DD bty]

  -- premise 2: the return type must be well kinded
  kc th tyA

  -- premises 4 and 5: we define a function to map over the
  -- branches that checks each is OK (and elaborates it)
  (y,mtchs) <- unbind bnd
  unless (length mtchs == length cons) $
     err [DS "Wrong number of pattern match branches for datatype", DD d]
  let
    checkBranch :: Match -> TcMonad Match
    checkBranch (c, cbnd) =
      case find (\(ConstructorDef  _ c' _) -> c'==c) cons of
        Nothing -> err [DD c, DS "is not a constructor of type", DD d]
        Just (ConstructorDef _  _ dumbdeltai)  ->
          do (deltai',ai) <- unbind cbnd
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
             return (c, bind deltai' eai)
  emtchs <- mapM checkBranch mtchs
  return (Case eb (bind y emtchs))

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
  context <- getTys
  let availableEqs = catMaybes $ map (\(x,th,ty) -> do guard (th==Logic)
                                                       (ty1,ty2) <- isTyEq ty
                                                       Just (x,ty1,ty2))
                                      context
  warn [DS "About to go off and try to prove:", DD (Goal (map (\(x,ty1,ty2) -> Sig x Logic (TyEq ty1 ty2)) availableEqs) 
                                               (TyEq ty1 ty2))]
  isTrue <- prove availableEqs (ty1,ty2)
  unless isTrue $
    err [DS "I was unable to prove:", DD (Goal (map (\(x,ty1,ty2) -> Sig x Logic (TyEq ty1 ty2)) availableEqs) 
                                               (TyEq ty1 ty2))]
  warn [DS "Successfully proved it, too!"]
  return TrustMe

ta th InferMe ty  = err [DS "I only know how to prove equalities, this goal has type", DD ty]

-- rule T_chk
ta th a tyB = do
  (ea,tyA) <- ts th a
  subtype th tyA tyB
    `catchError`
       \e -> err $ [DS "When checking term", DD a, DS "against type",
                    DD tyB, DS "the distinct type", DD tyA,
                    DS "was inferred, and it isn't a subtype:\n", DD e]
  return ea

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

         erasedTerm <- erase c   --fixme, maybe this check needs to be on an elaborated something or other.
         let runtimeVars = fv erasedTerm

         let chkTy (False,pf) _ = do
               (e,t) <- ts Logic pf
               return ((False,e),t)
             chkTy (True,pf) var = do
               --XX (e,_) <- ts Logic pf
               when (translate var `S.member` runtimeVars) $
                   err [DS "Equality proof", DD pf, DS "is marked erased",
                        DS "but the corresponding variable", DD var,
                        DS "appears free in the erased term", DD erasedTerm]
--               return ((True,e),
               return ((True,pf),pf) --fixme, the first pf should really be elaborated,
                                     -- but we probably need the context from the template to do that...

         (eas,atys) <- unzip <$> zipWithM chkTy as xs

         picky <- getFlag PickyEq
         let errMsg aty =
               err $ [DS "The second arguments to conv must be equality proofs,",
                      DS "but here has type", DD aty]


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
                _ -> errMsg aty
              ) atys

         let cA1 = substs (zip xs tyA1s) c
         let cA2 = substs (zip xs tyA2s) c
         eb <- ta th b cA1
         if picky then
            -- check c with extended environment
            -- Don't know whether these should be logical or programmatic
            let decls = zipWith (\ x t -> Sig x Logic t) xs ks in
              extendCtxs decls $ kc th c
           else
            -- check c after substitution
            kc th cA2
         return (Conv eb eas (bind xs c), cA2)

    -- rule T_annot
    ts' th (Ann a tyA) =
      do ea <- ta th a tyA
         return (Ann ea tyA, tyA)

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
     return $ AddCtx [dt]
     where cnames = map (\(ConstructorDef _ c _) -> c) cs

tcEntry dt@(AbsData _ delta th lev) =
  do kc th (telePi delta (Type lev))
     return $ AddCtx [dt]

tcEntry s@(Sig n th ty) = do
  duplicateTypeBindingCheck n ty
  kc th ty
  return $ AddHint s

tcEntry s@(Axiom n th ty) = do
  duplicateTypeBindingCheck n ty
  kc th ty
  return $ AddCtx [s]

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
          (Pos p' _) = ty'
          msg = [DS "Duplicate type signature ", DD ty,
                 DS "for name ", DD n,
                 DS "Previous typing at", DD p',
                 DS "was", DD ty']
       in
         extendSourceLocation p ty $ err msg

-----------------------
------ subtyping
-----------------------
subtype :: Theta -> Term -> Term -> TcMonad ()
subtype Program (Type _) (Type _) = return ()
subtype Logic (Type l1) (Type l2) =
  unless (l1 <= l2) $
    err [DS "In the logical fragment,", DD (Type l1),
         DS "is not a subtype of", DD (Type l2)]
subtype _ a b =
  unless (a' `aeqSimple` b') $
    err [DD a, DS "is not a subtype of", DD b]
  where a' = delPosParenDeep a
        b' = delPosParenDeep b


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
    
allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM p = liftM and . mapM p

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

uncurry3 :: (a->b->c->d) -> (a,b,c) -> d
uncurry3 f (x,y,z) = f x y z