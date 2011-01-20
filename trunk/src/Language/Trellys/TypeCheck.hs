{-# LANGUAGE TypeSynonymInstances, ExistentialQuantification, NamedFieldPuns, ParallelListComp, FlexibleContexts #-}
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

import Language.Trellys.GenericBind
import Generics.RepLib.Lib(subtrees)
import Generics.RepLib.R(Rep)
import Text.PrettyPrint.HughesPJ

import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)

import Data.Maybe
import Data.List
import qualified Data.Set as S

-- import System.IO.Unsafe (unsafePerformIO)

natType :: Term
natType = Con (string2Name "Nat")

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

-- | type analysis
ta :: Theta -> Term -> Term -> TcMonad Term
-- Position terms wrap up an error handler
ta th (Pos p t) ty = do
  ta th t ty `catchError`
         \(Err ps msg) -> throwError $ Err ((p,t):ps) msg
ta th tm (Pos _ ty) = ta th tm ty

ta th (Paren a) ty = liftM Paren $ ta th a ty  
ta th tm (Paren ty) = ta th tm ty

-- rule T_join
ta th (Join s1 s2) (TyEq a b) =
  do kc th (TyEq a b)
     (_,k1) <- ts Program a
     (_,k2) <- ts Program b
     picky <- getFlag PickyEq
     when (picky && not (k1 `aeq` k2)) $
         err [DS "Cannot join terms of different types:", DD a,
         DS "has type", DD k1, DS "and", DD b, DS "has type", DD k2]
     t1E <- erase =<< substDefs a
     t2E <- erase =<< substDefs b
     joinable <- join s1 s2 t1E t2E
     unless joinable $
       err [DS "The erasures of terms", DD a, DS "and", DD b,
            DS "are not joinable."]
     return (Join s1 s2)

-- rule T_contra
ta th (Contra a) b =
  do kc th b
     (ea, tyA) <- ts Logic a
     case isTyEq tyA of
       Just (cvs1, cvs2) ->
         case (splitApp cvs1, splitApp cvs2) of
           ((Con c1, vs1), (Con c2, vs2)) ->
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
       _ -> err [DS "The argument to contra must be an equality proof.",
                 DS "Here its type is", DD tyA]
       

-- rule T_abort
ta Logic Abort _ = err [DS "abort must be in P."]
ta Program Abort tyA = do kc Program tyA ; return Abort

-- Rules T_lam1 and T_lam2
ta th (Lam lep lbody) a@(Arrow ath aep tyA abody) = do

  -- First check the arrow type for well-formedness
  kc th a

  -- pull apart the bindings and make sure the epsilons agree
  Just (x,body,_,tyB) <- unbind2 lbody abody

  when (lep /= aep) $
       err ([DS "Lambda annotation", DD lep,
             DS "does not match arrow annotation", DD aep])

  -- typecheck the function body
  ebody <- extendCtx (Sig x ath tyA) (ta th body tyB)

  -- perform the FV and value checks if in T_Lam2
  bodyE <- erase body
  when (lep == Erased && x `S.member` fv bodyE) $
       err [DS "ta: In implicit lambda, variable", DD x,
            DS "appears free in body", DD body]
  when (th == Program && lep == Erased && (not $ isValue body)) $
       err [DS "ta : The body of an implicit lambda must be a value",
            DS "but here is:", DD body]
  return (Lam lep (bind x ebody))

-- rules T_rnexp and T_rnimp
ta _ (NatRec ep binding) (Arrow ath aep nat abnd) = do
  kc Logic (Arrow ath aep nat abnd)

  unless (ath == Logic) $
    err [DS "ta: recnat defines a function which takes a logical argument,",
         DS "here a computational argument was specified"]

  unless (nat `aeq` natType) $
     err [DS "ta: expecting argument of recnat to be Nat got ", DD nat]

  unless (ep == aep) $
     err [DS "ta : expecting argument of recnat to be", DD aep,
          DS "got", DD ep]
  (dumbvar,dumbbody) <- unbind abnd
  ((f,y),a) <- unbind binding
  -- to get the body "tyB" as it appears on paper, we must replace the
  -- extra variable we got from opening the binding
  let tyB = subst dumbvar (Var y) dumbbody

  -- next we must construct the type A.  we need new variables for x and z
  x <- fresh (string2Name "x")
  z <- fresh (string2Name "z")
  let xTyB = subst y (Var x) tyB
      eqType = TyEq (Var y)
                    (App Runtime (Con $ string2Name "Succ") (Var x))

      tyA = Arrow Logic ep natType (bind x
                  (Arrow Logic Erased eqType (bind z
                         xTyB)))
  -- Finally we can typecheck the fuction body in an extended environment
  ea <- extendCtx (Sig f Logic tyA) $
          extendCtx (Sig y Logic natType) $ ta Logic a tyB
  -- in the case where ep is Erased, we have the two extra checks:
  aE <- erase a
  when (ep == Erased && y `S.member` fv aE) $
       err [DS "ta: In implicit recnat, variable", DD y,
            DS "appears free in body", DD a]
  when (ep == Erased && (not $ isValue a)) $
       err [DS "ta : The body of an implicit natrec must be a value",
            DS "but here is:", DD a]
  return (NatRec ep (bind (f,y) ea))

-- rules T_rexp and T_rimp
ta Logic (Rec _ _) _ =
  err [DS "rec must be P."]

ta Program (Rec ep binding) fty@(Arrow ath aep tyA abnd) = do
  kc Program (Arrow ath aep tyA abnd)
  unless (ep == aep) $
         err [DS "ta : expecting argument of rec to be",
              DD aep, DS ", got", DD ep]

  (dumby,dumbbody) <- unbind abnd
  ((f,y),a) <- unbind binding
  let tyB = subst dumby (Var y) dumbbody

  ea <- extendCtx (Sig f Program fty) $
          extendCtx (Sig y ath tyA) $
            ta Program a tyB

  -- perform the FV and value checks if in T_RecImp
  aE <- erase a
  when (ep == Erased && y `S.member` fv aE) $
       err [DS "ta: In implicit rec, variable", DD y,
            DS "appears free in body", DD a]
  when (ep == Erased && (not $ isValue a)) $
       err [DS "ta : The body of an implicit rec must be a value",
            DS "but here is:", DD a]
  return (Rec ep (bind (f,y) ea))

-- rule T_case
ta th (Case b bnd) tyA = do
  -- premises 1, 3 and 4: we check that the scrutinee is the element of some
  -- datatype defined in the context
  (eb,bty) <- ts th b
  (d,bbar,delta,cons) <-
    case splitApp bty of
      (Con d, apps) -> do
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
                   DS "must be a member of a datatype, but is not"]
      _ -> err [DS "Scrutinee ", DD b,
                DS "must be a member of a datatype, but is not"]

  -- premise 2: the return type must be well kinded
  kc th tyA

  -- premises 4 and 5: we define a function to map over the
  -- branches that checks each is OK (and elaborates it)
  (y,mtchs) <- unbind bnd
  unless (   (length mtchs == length cons)
          && (length (nub $ map fst cons) == length cons)) $
     err [DS "Wrong number of pattern match branches for datatype", DD d]
  let
    checkBranch :: Match -> TcMonad Match
    checkBranch (c, cbnd) =
      case lookup c cons of
        Nothing -> err [DD c, DS "is not a constructor of type", DD d]
        Just ctyp ->
          do (deltai',ai) <- unbind cbnd
             (dumbdeltai,_) <- splitPi ctyp
             unless (length deltai' == length dumbdeltai) $
                err [DS "wrong number of argument variables for constructor",
                     DD c, DS "in pattern match."]
             unless (   (map snd deltai')
                     == map (\(_,_,_,e) -> e) dumbdeltai) $
                err [DS "wrong epsilons on argument variables for constructor",
                     DD c, DS "in pattern match."]
             let deltai = swapTeleVars dumbdeltai (map fst deltai')
                 subdeltai = substs (teleVars delta) (map fst bbar) deltai
                 eqtype = TyEq b (teleApp (multiApp (Con c) bbar) deltai)
             -- premise 5
             eai <- extendCtx (Sig y Logic eqtype) $
                      extendCtxTele subdeltai $ ta th ai tyA
             -- premise 6
             aE <- erase ai
             let shouldBeNull = S.fromList (y : domTeleMinus delta) `S.intersection` fv aE
             unless (S.null shouldBeNull) $
               err [DS "The constructor arguments ",
                    DS (show shouldBeNull),
                    DS "should not appear in the erasure of ", DD ai,
                    DS "because they bind compiletime variables."]
             return (c, bind deltai' eai)
  emtchs <- mapM checkBranch mtchs
  return (Case eb (bind y emtchs))
  
-- implements the checking version of T_let1 and T_let2
ta th (Let th' ep a bnd) tyB =
 do -- begin by checking syntactic -/L requirement and unpacking binding
    when (ep == Erased && th' == Program) $
       err [DS "Implicit lets must bind logical terms."]
    ((x,y),b) <- unbind bnd
    -- premise 1
    (ea,tyA) <- ts th' a
    -- premise 2
    eb <- extendCtx (Sig y Logic (TyEq (Var x) a)) $
            extendCtx (Sig x th' tyA) $
              ta th b tyB
    -- premise 3
    kc th tyB
    -- premises 4 and 5
    bE <- erase b
    when (y `S.member` fv bE) $
      err [DS "The equality variable bound in a let is not allowed to",
           DS "appear in the erasure of the body, but here", DD y,
           DS "appears in the erasure of", DD b]
    when (ep == Erased && x `S.member` fv bE) $
      err [DS "The variables bound in an implicit let are not allowed to",
           DS "appear in the erasure of the body, but here", DD x,
           DS "appears in the erasure of", DD b]
    unless (th' <= th) $
      err [DS "Program variables can't be bound with let expressions in",
           DS "Logical contexts because they would be normalized when the",
           DS "expression is."]
    return (Let th' ep ea (bind (x,y) eb))

-- rule T_chk
ta th a tyB = do 
  (ea,tyA) <- ts th a
  subtype th tyA tyB
    `catchError`
       \e -> err $ [DS "When checking term", DD a, DS "against type",
                    DD tyB, DS "the distinct type", DD tyA,
                    DS "was inferred, and it isn't a subtype:\n", DD e]
  return ea

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
     return $ (etsTm, delPosParen typ)
  where
    ts' :: Theta -> Term -> TcMonad (Term,Term)
    ts' th (Pos p t) =
      ts' th t `catchError`
         \(Err ps msg) -> throwError $ Err ((p,t):ps) msg

    ts' th (Paren a) = 
      do (ea,ty) <- ts' th a
         return (Paren ea, ty)

    -- Rule T_var
    ts' th (Var y) =
      do x <- lookupTy y
         case x of
           Just (th',ty) -> do
             unless (th' <= th || isFirstOrder ty) $
               err [DS "Variable", DD y, DS "is programmatic, but it was checked",
                    DS "logically."]
             return (Var y, ty)
           Nothing -> err [DS "The variable", DD y, DS "was not found."]

    -- Rule T_type
    ts' _ (Type l) = return (Type l,  Type (l + 1))

    -- Rules T_pi and T_pi_impred
    ts' th (Arrow th' ep tyA body) =
      do (x, tyB) <- unbind body
         (etyA, tytyA) <- ts th tyA
         (etyB, tytyB) <- extendCtx (Sig x th' tyA) $ ts th tyB
         case (isType tytyA, isType tytyB) of
           (Just _, Just 0) -> return $ (Arrow th' ep etyA (bind x etyB), Type 0)
           (Just n, Just m) -> return $ (Arrow th' ep etyA (bind x etyB), Type (max n m))
           (Just _, _)      -> err [DD tyB, DS "is not a type."]
           (_,_)            -> err [DD tyA, DS "is not a type."]

    -- Rules T_tcon, T_acon and T_dcon
    ts' th (Con c) =
      do typC <- lookupCon c
         case typC of
           (Left (delta, th', lev, _)) ->
             do unless (th' <= th) $
                  err [DS "Constructor", DD c,
                       DS "is programmatic, but it was checked logically."]
                return (Con c, telePi (map (\(t,a,b,_) -> (t,a,b,Runtime)) delta)
                                      (Type lev))
           (Right (delta, th', tm)) ->
             do unless (th' <= th) $
                  err [DS "Constructor", DD c,
                       DS "is programmatic, but it was checked logically."]
                return $ (Con c, telePi (map (\(t,a,b,_) -> (t,a,b,Erased)) delta) tm)

    -- rule T_app
    ts' th tm@(App ep a b) =
      do (ea,tyArr) <- ts th a
         case isArrow tyArr of
           Nothing -> err [DS "ts: expected arrow type, for term ", DD a,
                           DS ". Instead, got", DD tyArr]
           Just (th',epArr,tyA,bnd) -> do
             (x,tyB) <- unbind bnd
             unless (ep == epArr) $
               err [DS "Application annotation", DD ep, DS "in", DD tm,
                    DS "doesn't match arrow annotation", DD epArr]

             let b_for_x_in_B = subst x b tyB
             -- To implement app1 and app2 rules, we first try to
             -- check the argument Logically and check the resulting
             -- substitution.  If either fails, we would have to use
             -- App2.  In that case, th' must be Program and the argument
             -- must be a value.
             eb <- ((kc th b_for_x_in_B >> ta Logic b tyA)
                    `catchError`
                      \e ->
                        if th' == Logic then throwError e else
                          do unless (isValue b) $
                                err [DS "When applying to a term with classifier",
                                     DS "P, it must be a value, but",
                                     DD b, DS "is not."]
                             ta Program b tyA)
             return (App ep ea eb, b_for_x_in_B)

    -- rule T_eq
    ts' _ (TyEq a b) = do
      (ea,_) <- ts' Program a
      (eb,_) <- ts' Program b
      return $ (TyEq ea eb, Type 0)

    -- rule T_conv
    ts' th (Conv b as bnd) =
      do (xs,c) <- unbind bnd
         (eas,atys) <- liftM unzip (mapM (ts Logic) as)
         picky <- getFlag PickyEq
         let errMsg aty =
               err $ [DS "The second arguments to conv must be equality proofs,",
                      DS "but here has type", DD aty]
--         let isTyEq' aTy = maybe (errMsg aTy) return (isTyEq aTy)
--         (tyA1s,tyA2s) <- liftM unzip $ mapM isTyEq' atys
         (tyA1s,tyA2s, ks) <- liftM unzip3 $ mapM (\aty -> do
              case isTyEq aty of
                Just (tyA1, tyA2) -> do
                 (_,k1) <- ts Program tyA1
                 (_,k2) <- ts Program tyA2
                 when (picky && (not (k1 `aeq` k2))) $ err
                   [DS "Terms ", DD tyA1, DS "and", DD tyA2,
                    DS " must have the same type when used in conversion.",
                    DS "Here they have types: ", DD k1, DS "and", DD k2,
                    DS "respectively."]
                 return (tyA1, tyA2, k1)
                _ -> errMsg aty) atys
         let cA1 = substs xs tyA1s c
         let cA2 = substs xs tyA2s c
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
    ts' th (Let th' ep a bnd) =
     do -- begin by checking syntactic -/L requirement and unpacking binding
        when (ep == Erased && th' == Program) $
          err [DS "Implicit lets must bind logical terms."]
        ((x,y),b) <- unbind bnd
        -- premise 1
        (ea,tyA) <- ts th' a
        -- premise 2
        (eb,tyB) <- extendCtx (Sig y Logic (TyEq (Var x) a)) $
                      extendCtx (Sig x th' tyA) $
                        ts th b
        -- premise 3
        kc th tyB
        -- premises 4 and 5
        bE <- erase b
        when (y `S.member` fv bE) $
          err [DS "The equality variable bound in a let is not allowed to",
               DS "appear in the erasure of the body, but here", DD y,
               DS "appears in the erasure of", DD b]
        when (ep == Erased && x `S.member` fv bE) $
          err [DS "The variables bound in an implicit let are not allowed to",
               DS "appear in the erasure of the body, but here", DD x,
               DS "appears in the erasure of", DD b]
        unless (th' <= th) $
          err [DS "Program variables can't be bound with let expressions in",
               DS "Logical contexts because they would be normalized when the",
               DS "expression is."]
        return (Let th' ep ea (bind (x,y) eb), tyB)

    ts' _ tm = err $ [DS "Sorry, I can't infer a type for:", DD tm,
                      DS "Please add an annotation."]


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
tcModule defs m' = do checkedEntries <- extendCtxs importedDefs $ foldr tcE (return []) (moduleEntries m')
                      return m'{ moduleEntries = checkedEntries }
  where d `tcE` m = do
          -- Extend the Env per the current Decl before checking
          -- subsequent Decls.
          x <- tcEntry d
          case x of
            AddHint  hint  -> extendHints hint m
                           -- Add decls to the Decls to be returned
            AddCtx decls -> liftM (decls++) (extendCtxs decls m)
        -- Get all of the defs from imported modules (this is the env to check current module in)
        importedDefs = concat [moduleEntries mod | mod <- defs, (ModuleImport (moduleName mod)) `elem` moduleImports m']

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
              msg' = disp [DS "when checking the term ", DD term,
                           DS "against the signature", DD ty]
          in do
            eterm <- ta theta term ty `catchError` handler
            -- If we already have a type in the environment, due to a sig
            -- declaration, then we don't add a new signature.
            --
            -- Put the elaborated version of term into the context.
            return $ AddCtx [Sig n theta ty, Def n eterm]
    die term' =
      let (Pos p t) = term
          (Pos p' _) = term'
          msg = disp [DS "Multiple definitions of", DD n,
                      DS "Previous definition at", DD p']
      in do throwError $ Err [(p,t)] msg

-- rule Decl_data
tcEntry dt@(Data t delta th lev cs) =
  do ---- Premise 1
     kc th (telePi delta (Type lev))

     ---- Premise 2 in two parts.
     ---- Part 1: make sure the return type of each constructor is right
     let
       checkConRet :: TName -> Term -> TcMonad ()
       checkConRet c tm =
         do (_,ret) <- splitPi tm
            let (t',tms) = splitApp ret
                correctApps = map (\(v,_,_,_) -> (Var v,Runtime)) delta
            unless (    (Con t `aeq` t')
                     && (tms `aeq` correctApps)) $
              err [DS "Constructor", DD c,
                   DS "must have return type",
                   DD (multiApp (Con t) correctApps)]

     mapM_ (uncurry checkConRet) cs

     -- Part 2: type check the whole constructor type
     extendCtx (AbsData t delta th lev) $
       mapM_ (\(_,tyAi) -> ta th (telePi delta tyAi) (Type lev)) cs

     -- Premise 3: check that types are strictly positive.
     mapM_ (positivityCheck t) cs

     ---- finally, add the datatype to the env and perform action m
     return $ AddCtx [dt]

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
          msg = disp [DS "Duplicate type signature ", DD ty, 
                      DS "for name ", DD n,
                      DS "Previous typing at", DD p',
                      DS "was", DD ty']
       in
         throwError $ Err [(p,ty)] msg

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
  unless (a `aeq` b) $
    err [DD a, DS "is not a subtype of", DD b]

isFirstOrder :: Term -> Bool
isFirstOrder (TyEq _ _) = True
isFirstOrder (Pos _ ty) = isFirstOrder ty
isFirstOrder (Paren ty) = isFirstOrder ty
isFirstOrder ty = ty `aeq` natType

--debug n v = when False (liftIO (putStr n) >> liftIO (print v))
--debugNoReally n v = when True (liftIO (putStr n) >> liftIO (print v))


-- Positivity Check

-- | Determine if a data type only occurs in strictly positive positions in a
-- constructor's arguments.

positivityCheck
  :: (Rep b, Fresh m, Disp d, MonadError Err m) =>
     Name b -> (d, Term) -> m ()
positivityCheck tName (cName,ty)  = do
  (tele,_) <- splitPi ty
  _ <- mapM checkBinding tele
  return ()
 `catchError` \(Err ps msg) ->  throwError $ Err ps (msg $$ msg')
  where checkBinding (_,teleTy,Logic,_) = occursPositive tName teleTy
        checkBinding _ = return True
        msg' = text "when checking the constructor" <+> disp cName

occursPositive
  :: (Rep b, Fresh m, MonadError Err m) => Name b -> Term -> m Bool
occursPositive tName (Pos p ty) = do
  occursPositive tName ty `catchError`
         \(Err ps msg) -> throwError $ Err ((p,ty):ps) msg

occursPositive tName (Paren ty) = occursPositive tName ty
occursPositive tName aty@(Arrow _ _ _ _) = do
  (tele,_) <- splitPi aty
  let tys = [ty | (_,ty,_,_) <- tele]
      vars = S.unions $ map fv tys
      ok = not $ tName `S.member` vars
  unless ok $ err [DD tName, DS "occurs in non-positive position"]
  return True

occursPositive tName ty = do
  let children = subtrees ty
  res <- mapM (occursPositive tName) children
  return $ and res












