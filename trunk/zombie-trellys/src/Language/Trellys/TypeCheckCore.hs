-- Note: need to do ":cd ../.." in *haskell* window to make things work.

{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    UndecidableInstances, ViewPatterns, TupleSections #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

module Language.Trellys.TypeCheckCore (aTcModules, aTs, aKc, aGetTh, isEFirstOrder) where

import Data.List (find)
import qualified Data.Set as S
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)
import Control.Applicative

import qualified Generics.RepLib as RL

import Language.Trellys.Error
import Language.Trellys.Options
import Language.Trellys.Environment -- (Env, err, lookupTy, lookupTCon, lookupDCon, extendCtx)
import Language.Trellys.GenericBind
import Language.Trellys.Syntax
import Language.Trellys.OpSem (isEValue, erase, eraseToHead, join)
import Language.Trellys.TypeMonad

-------------------
-------------------
-- Typechecking!
-------------------
-------------------

coreErr :: (MonadReader Env m, MonadError Err m) => [D] -> m b
coreErr msg = do
  gamma <- getLocalCtx
  err $ [DS "Internal error: ill-typed core term."] 
        ++ msg
        ++ [DS "In context", DD gamma]
        
-- Given an environment and a theta, we synthesize a type and a theta or fail.
--  Since the synthesized type is "very annotated", this is a bit like regularity.
aTs :: ATerm -> TcMonad (Theta, ATerm)
aTs (AVar x) = maybeUseFO (AVar x) =<< (lookupTy x)

aTs (AUniVar x ty) = do 
  secondPass <- getFlag SecondPass
  if secondPass
    then coreErr [DS "Encountered an uninstantiated unification variable", DD x, DS "of type", DD ty]
    -- todo, the Logic is probably wrong, maybe need to to something smarter.
    else return (Logic,ty)

aTs (ACumul a j) = do
 (th, aTy) <- aTs a
 ty <- erase aTy
 case ty of
   (EType i) | i <= j -> return $ (th,AType j)
   _ -> coreErr [DS "Subterm of ACulum should be a type but is", DD aTy]

aTs (AType i) = return $ (Logic, AType (i+1))

aTs deriv@(AUnboxVal a) = do
  ea <- erase a
  unless (isEValue ea) $
    coreErr [DS "Argument of AUnboxVal should be a value, but is", DD a, DS $"i.e. " ++ show a]
  (_, atTy) <- aTs a
  case eraseToHead atTy of
    (AAt ty th) -> do aKc ty; return (th, ty)
    _  -> coreErr [DS "Argument of AUnboxVal should have an @-type, but has type", DD atTy,
                   DS ("\n when checking (" ++ show deriv ++ ")") ]

aTs (ATCon c idxs) = do
  (tys, i, _) <- lookupTCon c
  aTcTeleLogic (map (,Runtime) idxs) tys
  return (Logic, AType i)

aTs (ADCon c idxs args) = do 
  (tyc, indx_tys, (AConstructorDef _ arg_tys)) <- lookupDCon c 
  th <- aTcTele (map (,Runtime) idxs ++ args) (aAppendTele indx_tys arg_tys)
  aKc (ATCon (translate tyc) idxs)
  return (th, ATCon (translate tyc) idxs)

aTs  (AArrow ex ep bnd) = do
  ((x, unembed -> a), b) <- unbind bnd
  fo <- isEFirstOrder <$> (erase a)
  unless fo $ do
    coreErr [DS "The domain of an arrow should be first-order, but here it is", DD a]
  tya <- aTsLogic a
  tyb <- extendCtx (ASig x Program a) $ aTsLogic b
  case (tya, tyb) of
    (AType i, AType j) -> return (Logic, AType (max i j))
    (_, AType _) -> coreErr [DS "domain of an arrow should be a type, but here is", DD tya]
    (_, _) -> coreErr [DS "range of an arrow should be a type, but here is", DD tyb]

aTs (ALam (eraseToHead -> (AArrow ex epTy bndTy))  ep bnd) = do
  unless (epTy == ep) $
    coreErr [DS "ALam ep"]
  aKc (AArrow ex epTy bndTy)  
  Just ((x , unembed -> aTy), bTy , _, b) <- unbind2 bndTy bnd
  (th, bTy') <- extendCtx (ASig x Program aTy) $ aTs b
  bTyEq <- aeq <$> (erase bTy) <*> (erase bTy')
  unless bTyEq $ do
    bTyErased  <- erase bTy
    bTyErased' <- erase bTy'
    coreErr [DS "ALam annotation mismatch, function body was annotated as", DD bTyErased,
             DS "but checks at", DD bTyErased',
             DS "The full annotation was", DD (AArrow ex epTy bndTy)]
  return $ (th, AArrow ex epTy bndTy)

aTs (ALam ty _ _) = coreErr [DS "ALam malformed annotation, should be an arrow type but is", DD ty]

aTs (AApp ep a b ty) = do
  (tha, tyA) <- aTs a
  (thb, tyB) <- aTs b
  aKc ty
  case eraseToHead tyA of
    AArrow _ ep' bnd -> do
      unless (ep == ep') $
        coreErr [DS "AApp ep mismatch"]
      when (ep == Erased && thb == Program) $
        coreErr [DS "AApp: an erased argument must terminate, but", DD b, DS "checks at P"]        
      ((x, unembed -> tyB'), tyC) <- unbind bnd
      tyBEq <- aeq <$> erase tyB <*> erase tyB'
      unless tyBEq $
        coreErr [DS "AApp dom mismatch", DD tyB, DS "vs", DD tyB']
      tyEq <- aeq <$> erase ty <*> erase (subst x b tyC)
      unless tyEq $ 
        coreErr [DS "AApp annotation mismatch. Application has type", DD (subst x b tyC), 
                 DS "but was annotated as", DD ty]
      return (max tha thb, ty)
    _ -> coreErr [DS "AApp: The term being applied,", DD a, DS "should have an arrow type, but here has type", DD tyA]

aTs (AAt a th') = do
  aTy <- aTsLogic a
  case eraseToHead aTy of 
    AType i -> return $ (Logic, AType i)
    _ -> coreErr [DS "The argument to AAt should be a type, but it is", DD a, DS "which has type", DD aTy]

aTs (ABox a th') = do
  (th, aTy) <- aTs a
  isVal <- isEValue <$> erase a
  case th of 
    Logic                  -> return (Logic, AAt aTy th')
    Program | isVal        -> return (Logic, AAt aTy th')
    Program | th'==Program -> return (Program, AAt aTy th')
    _ -> coreErr [DS "in ABox,", DD a, DS "should check at L but checks at P"]

aTs (AAbort aTy) = do
  aKc aTy
  return (Program, aTy)

aTs (ATyEq a b) = do
  _ <- aTs a
  _ <- aTs b
  return (Logic, AType 0)

aTs (AJoin a i b j) = do
  aKc (ATyEq a b)
  aE <- erase =<< substDefs a
  bE <- erase =<< substDefs b
  joinable <- join i j aE bE
  unless joinable $
    coreErr [DS "AJoin: not joinable"]
  return (Logic, ATyEq a b)

aTs (AConv a prfs bnd ty) = do
  (xs, template) <- unbind bnd
  etemplate <- erase template
  let runtimeVars = fv etemplate
  (th, aTy) <- aTs a
  unless (length xs == length prfs) $
    coreErr [DS "AConv length mismatch"]
  eqs <-  let processPrf _ (pf,Runtime) = do
                              pfTy <- aTsLogic pf
                              case eraseToHead pfTy of
                                ATyEq a1 a2 -> return (a1, a2)
                                _           -> coreErr [DD pf, DS "should be a proof of an equality, but has type",
                                                        DD pfTy,
                                                        DS "(when checking the conv expression", DD (AConv a prfs bnd ty), DS ")"]
              processPrf x (ATyEq a1 a2, Erased) = do
                              when (translate x `S.member` runtimeVars) $
                                   coreErr [DS "AConv not erased var"]
                              return (a1, a2)
              processPrf _ (_, Erased) = coreErr [DS "AConv malformed irrelevant eq"]
           in zipWithM processPrf xs prfs
  let aTy1 = substs (zip xs (map fst eqs)) template
  let aTy2 = substs (zip xs (map snd eqs)) template
  fromEq <- aeq <$> erase aTy <*> erase aTy1
  toEq   <- aeq <$> erase ty  <*> erase aTy2
  unless fromEq $
    coreErr [DS "AConv: the term", DD a, DS "has type", DD aTy,
             DS "but substituting the LHSs of the equations into the template creates the type", DD aTy1]
  unless toEq $ 
    coreErr [DS "AConv: the conv-expression was annotated as", DD ty, 
             DS "but substituting the RHSs of the equations into the template creates the type", DD aTy2]
  aKc ty
  maybeUseFO a (th, ty)

-- Todo: This currently only considers head-forms of data
-- constructors, but for the annotated operational semantics, this
-- will need to consider headforms of all flavours of types.
aTs (AContra a ty) = do 
  aKc ty
  aTy <- aTsLogic a
  eaTy <- erase aTy
  case eaTy of 
    ETyEq (EDCon c1 args1) (EDCon c2 args2) -> do
      unless (c1 /= c2) $
        coreErr [DS "AContra Not unequal constructors"]
      unless (all isEValue args1 && all isEValue args2) $
        coreErr [DS "AContra not values"]
      return (Logic, ty)
    _ -> coreErr [DS "AContra not equality"]
   
aTs (AInjDCon a i) = do
  aTy <- aTsLogic a
  case eraseToHead aTy of
     ATyEq (ADCon c _ args) (ADCon c' _ args') -> do
       unless (c == c') $
         coreErr [DS "AInjDCon: the term", DD a, 
                  DS "should prove an equality where both sides are headed by the same data constructor, but in ", DD aTy, DS "the constructors are not equal"]
       eargs <- mapM (erase . fst) args
       eargs' <- mapM (erase . fst) args'
       unless (all isEValue eargs && all isEValue eargs') $
         coreErr [DS "AInjDCon: not all constructor arguments in", DD aTy, DS "are values."]
       unless (length args == length args') $
         coreErr [DS "AInjDCon: the two sides of", DD aTy, DS "have different numbers of arguments"]
       unless (i < length args) $
         coreErr [DS "AInjDCon: the index", DD i, DS "is out of range"]
       return (Logic, ATyEq (fst (args !! i)) (fst (args' !! i)))
     _ -> coreErr [DS "AInjDCon: the term", DD a, 
                   DS"should prove an equality of datatype constructors, but it has type", DD aTy]

aTs (ASmaller a b)  = do
  _ <- aTs a
  _ <- aTs b
  return (Logic, AType 0)

aTs (AOrdAx pf a1) = do 
  pfTy <- aTsLogic pf
  _ <- aTs a1
  ea1 <- erase a1
  case eraseToHead pfTy of 
    (ATyEq b1 (ADCon c params b2s)) -> do
       eb1 <- erase b1 
       eb2s <- mapM (erase . fst) b2s
       unless (any (aeq ea1) eb2s) $
         coreErr [DS "The term", DD a1, DS "is not one of the subterms appearing in RHS of", DD pfTy]
       return $ (Logic, ASmaller a1 b1)
    _ -> coreErr [DS "AOrdAx badeq"]
        
aTs (AOrdTrans a b) = do
  tya <- aTsLogic a
  tyb <- aTsLogic b
  case (eraseToHead tya, eraseToHead tyb) of
    (ASmaller t1 t2, ASmaller t2' t3') | t2 `aeq` t2' ->
       return $ (Logic, ASmaller t1 t3')
    _ -> coreErr [DS "The subproofs of AOrdTrans do not prove inequalities of the right type."]

aTs (AInd (eraseToHead -> (AArrow ex epTy bndTy)) ep bnd) = do
  unless (epTy == ep) $
    coreErr [DS "AInd ep"]
  aKc (AArrow ex epTy bndTy)
  ((y, unembed -> aTy), bTy) <-unbind bndTy
  ((f,dumby), dumbb) <- unbind bnd
  let b = subst dumby (AVar y) dumbb
  when (ep == Erased) $ do
    runtimeVars <- fv <$> erase b
    when (translate y `S.member` runtimeVars) $ do
      erasedB <- erase b
      coreErr [DS "AInd: the variable", DD y, 
               DS "is marked erased, but it appears in an unerased position in the body", DD erasedB]
  x <- fresh (string2Name "x")
  z <- fresh (string2Name "z")
  let fTy =  AArrow Explicit
                    ep 
                    (bind (x, embed aTy)
                    (AArrow Explicit Erased (bind (z, embed (ASmaller (AVar x) (AVar y)))
                                            (subst y (AVar x) bTy))))
  bTy' <- extendCtx (ASig y Logic aTy) $
            extendCtx (ASig f Logic fTy) $
              aTsLogic b
  bTyEq <- aeq <$> erase bTy <*> erase bTy'
  unless bTyEq $
    coreErr [DS "AInd should have type", DD bTy, DS "but has type", DD bTy']
  return $ (Logic, AArrow ex epTy bndTy)

aTs (AInd ty _ _) = coreErr [DS "AInd malformed annotation, should be an arrow type but is", DD ty]  

aTs (ARec (eraseToHead -> (AArrow ex epTy bndTy)) ep bnd) = do
  unless (epTy == ep) $
    coreErr [DS "AInd ep"]
  aKc (AArrow ex epTy bndTy)
  ((y, unembed -> aTy), bTy) <- unbind bndTy
  ((f,dumby), dumbb) <- unbind bnd
  let b = subst dumby (AVar y) dumbb
  when (ep == Erased) $ do
    runtimeVars <- fv <$> erase b
    when (translate y `S.member` runtimeVars) $
      coreErr [DS "ARec Erased var"]
  (th',  bTy') <-
    extendCtx (ASig y Logic aTy) $
      extendCtx (ASig f Logic (AArrow ex epTy bndTy)) $
        aTs b
  bTyEq <- aeq <$> erase bTy <*> erase bTy'
  unless bTyEq $
    coreErr [DS "ARec annotation mismatch"]
  return $ (Program, AArrow ex epTy bndTy)
  
aTs (ARec ty _ _) = coreErr [DS "ARec malformed annotation, should be an arrow type but is", DD ty]  

aTs (ALet ep bnd) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  runtimeVars <- fv <$> erase b
  when (ep == Erased && (translate x) `S.member` runtimeVars) $
    coreErr [DS "ALet erased var"]
  (th',aTy) <- aTs a
  when (th' == Program && ep == Erased) $
    coreErr [DS "the bound term in ALet is P, so it cannot be erased"]
  (th,bTy) <- extendCtx (ASig x th' aTy) $ 
                 extendCtx (ASig xeq Logic (ATyEq (AVar x) a)) $ do
                  aTs b
  aKc bTy  --To check that no variables escape.
  return (max th th', bTy) --The max enforces that P vars can not be bound in an L context.

aTs (ACase a bnd ty) = do
  (xeq, mtchs) <- unbind bnd
  (th, aTy) <- aTs a
  aKc ty
  case aTy of 
    (ATCon c idxs) -> do
      tCon <- lookupTCon c
      case tCon of 
        (delta, _, Just cons) -> do
          unless (length mtchs == length cons) $
            coreErr [DS "ACase The case expression has", DD (length mtchs),
                     DS "branches, but the datatype", DD c, DS "has", DD (length cons), DS "constructors"]
          unless (aTeleLength delta == length idxs) $
            coreErr [DS "ACase malformed core term, this should never happen"]
          ths <- mapM (aTsMatch th ty (zip (binders delta) idxs) cons (\pat -> ASig xeq Logic (ATyEq a pat)))
                      mtchs
          return (max th (maximum (minBound:ths)), ty)     
        (_, _,  Nothing) -> coreErr [DS "ACase case on abstract type"]
    _ -> coreErr [DS "ACase not data"]

aTs (ADomEq a) = do
  (th, aTy) <- aTs a
  case aTy of
    ATyEq (AArrow _ eps bndTy) (AArrow _ eps' bndTy') | eps == eps' ->
      unbind2 bndTy bndTy' >>=
        maybe (coreErr [DS "ADomEq applied to incorrect equality type"])
              (\((_, unembed -> tyDom), _, (_, unembed -> tyDom'), _) ->
                return (th, ATyEq tyDom tyDom'))
    _ -> coreErr [DS "ADomEq not applied to an equality between arrow types"]

aTs (ARanEq a b) = do
  (th,  aTy) <- aTs a
  (th', bTy) <- aTs b
  case aTy of
    ATyEq (AArrow _ eps bndTy) (AArrow _ eps' bndTy') | th == th' && eps == eps' -> do
      unbindRes <- unbind2 bndTy bndTy'
      case unbindRes of
        Nothing -> coreErr [DS "ARanEq incorrect equality type"]
        Just ((tyVar, unembed -> tyDom), tyRan, (_, unembed -> tyDom'), tyRan') -> do
          domsEq <- aeq <$> erase tyDom <*> erase tyDom'
          unless domsEq $
            coreErr [DS "ARanEq applied to an equality between arrow types with different domains "]
          bTyEq <- aeq <$> erase bTy <*> erase tyDom
          unless bTyEq $
            coreErr [DS "ARanEq value has wrong type"]
          return (th, ATyEq (subst tyVar b tyRan) (subst tyVar b tyRan'))
    _ -> coreErr [DS "ARanEq not applied to an equality between arrow types"]

aTs (AAtEq a) = do
  (th, aTy) <- aTs a
  case aTy of
    ATyEq (AAt atTy th') (AAt atTy' th'') | th' == th'' -> return (th, ATyEq atTy atTy')
    _ -> coreErr [DS "AAtEq not applied to an equality between at-types"]

aTs (ANthEq i a) = do
  (th, aTy) <- aTs a
  case aTy of
    ATyEq (ATCon c as) (ATCon c' as')
      | c /= c'                 -> coreErr [DS "ANthEq between different data types"]
      | length as /= length as' -> coreErr [DS "ANthEq between mismatched ATCon lengths"]
      | i <= 0                  -> coreErr [DS "ANthEq at non-positive index"]
      | i > length as           -> coreErr [DS "ANthEq index out of range"]
      | otherwise               -> return $ (th, ATyEq (as !! i) (as' !! i))
    _ -> coreErr [DS "ANthEq not applied to an equality between type constructor applications"]

aTs (ATrustMe ty) = do
  aKc ty
  return (Logic, ty)

aTs (ASubstitutedFor a _) = aTs a

-- Synthesize a type and enforce that it can be checked at L, using FO if necessary.
aTsLogic :: ATerm -> TcMonad ATerm
aTsLogic a = do
  (th, aTy) <- aTs a
  case th of 
    Logic -> return aTy
    Program -> do
      ea <- erase a
      eaTy <- erase aTy
      if (isEValue ea && isEFirstOrder eaTy)
       then return aTy
       else coreErr [DS "The expression", DD a, DS "should check at L, but does not (and the first-order rule does not apply)"]

-- If a is a value and aTy is a first-order type, then change Program to Logic.
maybeUseFO :: ATerm -> (Theta,ATerm) -> TcMonad (Theta, ATerm)
maybeUseFO a (Logic,aTy) = return (Logic,aTy)
maybeUseFO a (Program, aTy) = do
  ea <- erase a
  eaTy <- erase aTy
  if (isEValue ea && isEFirstOrder eaTy)
    then return (Logic, aTy)
    else return (Program, aTy)

-- Compute the best theta that can be given to a term.
aGetTh :: ATerm -> TcMonad Theta
aGetTh a = do
  (th, _) <- aTs a
  return th

-- Check that a term is a type 
aKc :: ATerm  -> TcMonad ()
aKc t  = do
  (th,ty) <- aTs t
  ety <- erase ty
  case (th,ety) of
    (Logic,(EType _)) -> return ()
    (Program, _) -> coreErr [DD t, DS "should be a type that checks logically, but checks at P"]
    _            -> coreErr [DD t, DS "should be a type, but has type", DD ty]

-- Check that all types in a telescope are well-formed.
aKcTele :: ATelescope -> TcMonad ()
aKcTele AEmpty = return ()
aKcTele (ACons (unrebind->((x,unembed->ty,ep),rest))) = do
  aKc ty
  fo <- isEFirstOrder <$> (erase ty)
  unless fo $
     coreErr [DS "All types in a telescope needs to be first-order, but", DD ty, DS "is not"]
  extendCtx (ASig x Program ty) $ aKcTele rest
 
-- Check that the body of a match typecheck at the right type.
aTsMatch ::  Theta                -- the theta of the scrutinee
             -> ATerm             -- the type that the branch should check at.
             -> [(AName,ATerm)]   -- substitution for type indexes
             -> [AConstructorDef] -- the constructors of the datatype
             -> (ATerm -> ADecl)  -- the "scrutinee = pattern" equality, partially applied
             -> AMatch            -- the branch to check
             -> TcMonad Theta
aTsMatch th ty idxs cons xeq (AMatch c bnd) = do
  (xs, a) <- unbind bnd
  case find (\(AConstructorDef c' _) -> c'==c) cons of
    Nothing -> coreErr [DS "AMatch: Trying to match against the constructor", DD c,
                        DS "which is not a constructor of the datatype."]
    Just (AConstructorDef _ cargs) -> do
      unless (aTeleLength cargs == aTeleLength xs) $
        coreErr [DS "AMatch: Branch expects", DD (aTeleLength xs), DS "arguments",
                 DS "but the constructor", DD c, DS "has", DD (aTeleLength cargs), DS "arguments"]
      tyEq <- eqTele xs (substs idxs cargs)
      unless tyEq $
        coreErr [DS "The pattern variables to the constructor", DD c, DS "were annotated to have types", DD xs,
                 DS "but should have types", DD (substs idxs cargs)]
      extendCtxTele xs th $ 
        extendCtx (xeq (ADCon c (map snd idxs) (aTeleAsArgs xs))) $ do
         (th', ty') <- aTs a
         ety' <- erase ty'
         ety  <- erase ty
         unless (ety' `aeq` ety) $
           coreErr [DS "AMatch: Branch has type", DD ty', DS "but was expected to have type", DD ty]
         return th'


-- Compare two telescopes for equality up-to-alpha.
eqTele :: ATelescope -> ATelescope -> TcMonad Bool
eqTele AEmpty AEmpty = return True
eqTele AEmpty _  = return False
eqTele _  AEmpty = return False
eqTele (ACons (unrebind->((x,unembed->a,ep),tele))) (ACons (unrebind->((x',unembed->a',ep'),tele'))) = do
  ea  <- erase a
  ea' <- erase a'
  tyEq <- eqTele tele (subst x' (AVar x) tele')
  return $ (ea `aeq` ea') && (ep == ep') && tyEq

-- Check a list of terms against a telescope
aTcTele :: [(ATerm,Epsilon)] -> ATelescope -> TcMonad Theta
aTcTele [] AEmpty = return Logic
aTcTele ((t,ep1):ts) (ACons (unrebind->((x,unembed->ty,ep2),tele'))) = do
  unless (ep1==ep1) $
    coreErr [DS "aTcTele ep"]
  (th', ty') <- aTs t
  ety  <- erase ty
  ety' <- erase ty'
  unless (ety' `aeq` ety) $
    coreErr [DS "aTcTele: the expression",DD t,DS "should have type", DD ty,
             DS "but has type", DD ty']
  th <-  aTcTele ts (subst x t tele')
  return (max th th')
aTcTele _ _ = coreErr [DS "aTcTele telescope length mismatch"]

-- Same as acTcTele, but also require that the terms check logically.
aTcTeleLogic :: [(ATerm,Epsilon)] -> ATelescope -> TcMonad ()
aTcTeleLogic [] AEmpty = return ()
aTcTeleLogic ((t,ep1):ts) (ACons (unrebind->((x,unembed->ty,ep2),tele'))) = do
  unless (ep1==ep1) $
    coreErr [DS "aTcTeleLogic ep"]
  ty' <- aTsLogic t
  ety  <- erase ty
  ety' <- erase ty'
  unless (ety' `aeq` ety) $
    coreErr [DS "aTcTeleLogic: the expression",DD t,DS "should have type", DD ty,
             DS "but has type", DD ty']
  aTcTeleLogic ts (subst x t tele')
aTcTeleLogic _ _ = coreErr [DS "aTcTeleLogic telescope length mismatch"]

isEFirstOrder :: ETerm -> Bool
isEFirstOrder (ETyEq _ _)    = True
isEFirstOrder (ESmaller _ _) = True
isEFirstOrder (EAt _ _)      = True
isEFirstOrder (ETCon d _)    = True
isEFirstOrder (EType _)      = True
isEFirstOrder _              = False
             
----------------------------------------------
-- Typechecking an entire set of modules.
----------------------------------------------


aTcModules :: [AModule] -> TcMonad ()
aTcModules mods = aTcEntries (concatMap aModuleEntries mods) 

-- Fixme: this is not enough, it just checks that each entry has _some_ type, but it should already
-- catch some errors.
aTcEntries :: [ADecl] -> TcMonad ()
aTcEntries [] = return ()
aTcEntries (d@(ASig x th aTy) : rest) = do
  aKc aTy
  extendCtx d $ aTcEntries rest
aTcEntries (d@(ADef x a) : rest) = do
  _ <- aTs a
  extendCtx d $ aTcEntries rest
aTcEntries (d@(AData t delta lvl constructors) : rest) = do
  aKcTele delta
  extendCtx (AAbsData t delta lvl) $
            mapM_ (\(AConstructorDef c args) -> extendCtxTele delta Program $ aKcTele args) constructors
  mapM_ (aPositivityCheck t) constructors
  extendCtx d $ aTcEntries rest
aTcEntries (d@(AAbsData t delta lvl) : rest)  = do 
  aKcTele delta

aPositivityCheck:: (Fresh m, MonadError Err m, MonadReader Env m) =>
                   AName -> AConstructorDef -> m ()
aPositivityCheck x (AConstructorDef cName args)  = aPositivityCheckTele args
  where aPositivityCheckTele :: (Fresh m, MonadError Err m, MonadReader Env m) => ATelescope -> m ()
        aPositivityCheckTele AEmpty = return ()
        aPositivityCheckTele (ACons (unrebind->((_,unembed->ty,_),tele))) = do
            aOccursPositive cName ty
            aPositivityCheckTele tele

aOccursPositive  :: (Fresh m, MonadError Err m, MonadReader Env m) => 
                   AName -> ATerm -> m ()
aOccursPositive x (AArrow _ _ bnd) = do
 ((_,unembed->tyA), tyB) <- unbind bnd
 when (x `S.member` (fv tyA)) $
    err [DD x, DS "occurs in non-positive position"]
 aOccursPositive x tyB
aOccursPositive x ty = do
  let children = RL.subtrees ty
  mapM_ (aOccursPositive x) children
