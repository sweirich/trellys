-- Note: need to do ":cd ../.." in *haskell* window to make things work.

{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    UndecidableInstances, ViewPatterns, TupleSections #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

module Language.Trellys.TypeCheckCore (aTcModules, aTs, aKcAt, aKcAny, aGetTh) where

import Data.List (find)
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)
import Control.Applicative

import Language.Trellys.Error
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
aTs (AVar x) = lookupTy x

aTs (AFO a) = do
   (th, aTy) <- aTs a
   fo <- isEFirstOrder =<< (erase aTy)
   unless fo $
     coreErr [DS "Subterm of AFO should have a first-order type but has type", DD aTy]
   return (Logic, aTy)

aTs (ASquash a) = do
  (th, aTy) <- aTs a
  ty <- erase aTy 
  case ty of
    (EType _) -> return $ (Program, AType 0)
    _         -> coreErr [DS "Subterm of ASquash should be a type but is", DD aTy]

aTs (ACumul a j) = do
 (th, aTy) <- aTs a
 ty <- erase aTy
 case ty of
   (EType i) | i < j -> return $ (th,AType j)
   _ -> coreErr [DS "Subterm of ACulum should be a type but is", DD aTy]

aTs (AType i) = return $ (Logic, AType (i+1))

aTs deriv@(AUnboxVal a) = do
  ea <- erase a
  unless (isEValue ea) $
    coreErr [DS "Argument of AUnboxVal should be a value, but is", DD a]
  (_, atTy) <- aTs a
  case eraseToHead atTy of
    (AAt ty th) -> return (th, ty)
    _  -> coreErr [DS "Argument of AUnboxVal should have an @-type, but has type", DD atTy,
                   DS ("\n when checking (" ++ show deriv ++ ")") ]

aTs (ATCon c idxs) = do
  (tys, thData, i, _) <- lookupTCon c
  th <- aTcTele (map (,Runtime) idxs) tys
  return (max thData th, AType i)

aTs (ADCon c idxs args) = do 
  (tyc, indx_tys, thData, (AConstructorDef _ arg_tys)) <- lookupDCon c 
  th <- aTcTele (map (,Runtime) idxs ++ args) (indx_tys ++ arg_tys)
  return (max thData th, ATCon (translate tyc) idxs)

aTs  (AArrow ep bnd) = do
  ((x, unembed -> a), b) <- unbind bnd
  fo <- isEFirstOrder =<< (erase a)
  unless fo $ do
    coreErr [DS "The domain of an arrow should be first-order, but here it is", DD a]
  (tha, tya) <- aTs a
  (thb, tyb) <- extendCtx (ASig x Program a) $ 
                   aTs b
  case (tya, tyb) of
    (AType i, AType j) -> return (max tha thb, AType (max i j))
    (_, AType _) -> coreErr [DS "domain of an arrow should be a type, but here is", DD tya]
    (_, _) -> coreErr [DS "range of an arrow should be a type, but here is", DD tyb]

aTs (ALam (eraseToHead -> (AArrow epTy bndTy))  ep bnd) = do
  unless (epTy == ep) $
    coreErr [DS "ALam ep"]
  th1 <- aKc (AArrow epTy bndTy)  
  Just ((x , unembed -> aTy), bTy , _, b) <- unbind2 bndTy bnd
  (th2, bTy') <- extendCtx (ASig x Program aTy) $ aTs b
  bTyEq <- aeq <$> (erase bTy) <*> (erase bTy')
  unless bTyEq $ do
    bTyErased  <- erase bTy
    bTyErased' <- erase bTy'
    coreErr [DS "ALam annotation mismatch, function body was annotated as", DD bTyErased,
             DS "but checks at", DD bTyErased',
             DS "The full annotation was", DD (AArrow epTy bndTy)]
  return $ (max th1 th2, AArrow epTy bndTy)

aTs (ALam ty _ _) = coreErr [DS "ALam malformed annotation, should be an arrow type but is", DD ty]

aTs (AApp ep a b ty) = do
  (tha, tyA) <- aTs a
  (thb, tyB) <- aTs b
  thty <- aKc ty
  case tyA of
    AArrow ep' bnd -> do
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
      return (maximum [tha, thb, thty], ty)
    _ -> coreErr [DS "AApp not arrow"]

aTs (AAt a th') = do
  (tha, aTy) <- aTs a
  unless (tha <= th') $
    coreErr [DS "Argument of AAt should check at", DD th', 
             DS "but it has theta", DD tha,
             DS ("when checking " ++ show (AAt a th'))]
  case eraseToHead aTy of 
    AType i -> return $ (Logic, AType i)
    _ -> coreErr [DS "The argument to AAt should be a type, but it is", DD a, DS "which has type", DD aTy]

aTs (ABoxLL a th') = do
  (tha, aTy) <- aTs a
  unless (tha == Logic) $
    coreErr [DS "Argument to ABoxLL should check logically, but", DD a,
             DS "checks as Program"]
  return (Logic, AAt aTy th')

aTs (ABoxLV a th') = do
  aEVal <- isEValue <$> erase a
  unless aEVal $
    coreErr [DS "ABoxLV nonvalue"]
  (tha, aTy) <- aTs a
  return (Logic, AAt aTy th')

aTs (ABoxP a th') = do
  (th, aTy) <- aTs a
  unless (th <= th') $
    coreErr [DS "Argument of ABoxP should check at", DD th', 
             DS "but it has theta", DD th]
  return (Program, AAt aTy th')

aTs (AAbort aTy) = do
  aKcAny aTy
  return (Program, aTy)

aTs (ATyEq a b) = do
  _ <- aTs a
  _ <- aTs b
  return (Logic, AType 0)

aTs (AJoin a i b j) = do
  aKcAny (ATyEq a b)
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
                              (th', pfTy) <- aTs pf
                              case (th', pfTy) of
                                (Logic, ATyEq a1 a2) -> return (a1, a2)
                                (Program, _) -> 
                                    coreErr [DS "Equality proofs should check at L, but",
                                             DD pf, DS "checks at P"]
                                (Logic, _) -> coreErr [DD pf, DS "should be a proof of an equality, but has type",
                                                       DD pfTy]
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
  th' <- aKc ty
  return (max th th', aTy2)

aTs (AContra a ty) = do 
  aKcAny ty
  (th, aTy) <- aTs a
  unless (th == Logic) $
   coreErr [DS "The proof of contradiction", DD a, DS "should typecheck at L, but here checks at P"]
  eaTy <- erase aTy
  case eaTy of 
    ETyEq (EDCon c1 args1) (EDCon c2 args2) -> do
      unless (c1 /= c2) $
        coreErr [DS "AContra Not unequal constructors"]
      unless (all isEValue args1 && all isEValue args2) $
        coreErr [DS "AContra not values"]
      return (Logic, ty)
    _ -> coreErr [DS "AContra not equality"]
   
aTs (ASmaller a b)  = do
  _ <- aTs a
  _ <- aTs b
  return (Logic, AType 0)

aTs (AOrdAx pf a1) = do 
  (th, pfTy) <- aTs pf
  unless (th == Logic) $
    coreErr [DS "The proof to AOrdAx,", DD pf, DS "must typecheck at L"]
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
  (tha, tya) <- aTs a
  unless (tha == Logic) $
    coreErr [DS "The proof", DD a, DS "given to AOrdTrans should check at L but checks at P"]
  (thb, tyb) <- aTs b
  unless (thb == Logic) $
    coreErr [DS "The proof", DD b, DS "given to AOrdTrans should check at L but checks at P"]
  case (eraseToHead tya, eraseToHead tyb) of
    (ASmaller t1 t2, ASmaller t2' t3') | t2 `aeq` t2' ->
       return $ (Logic, ASmaller t1 t3')
    _ -> coreErr [DS "The subproofs of AOrdTrans do not prove inequalities of the right type."]

aTs (AInd (eraseToHead -> (AArrow epTy bndTy)) ep bnd) = do
  unless (epTy == ep) $
    coreErr [DS "AInd ep"]
  aKcAt Logic (AArrow epTy bndTy)
  ((y, unembed -> aTy), bTy) <-unbind bndTy
  ((f,dumby), dumbb) <- unbind bnd
  let b = subst dumby (AVar y) dumbb
  when (ep == Erased) $ do
    bIsVal <- isEValue <$> erase b
    unless bIsVal $
      coreErr [DS "AInd Erased nonvalue"]
    runtimeVars <- fv <$> erase b
    when (translate y `S.member` runtimeVars) $ do
      erasedB <- erase b
      coreErr [DS "AInd: the variable", DD y, 
               DS "is marked erased, but it appears in an unerased position in the body", DD erasedB]
  x <- fresh (string2Name "x")
  z <- fresh (string2Name "z")
  let fTy =  AArrow ep (bind (x, embed aTy)
                       (AArrow Erased (bind (z, embed (ASmaller (AVar x) (AVar y)))
                                            (subst y (AVar x) bTy))))
  (th', bTy') <-
    extendCtx (ASig y Logic aTy) $
      extendCtx (ASig f Logic fTy) $
        aTs b
  unless (th' == Logic) $
    coreErr [DS "AInd: body should check at L, but is P"]
  bTyEq <- aeq <$> erase bTy <*> erase bTy'
  unless bTyEq $
    coreErr [DS "AInd should have type", DD bTy, DS "but has type", DD bTy']
  return $ (Logic, AArrow epTy bndTy)

aTs (AInd ty _ _) = coreErr [DS "AInd malformed annotation, should be an arrow type but is", DD ty]  

aTs (ARec (eraseToHead -> (AArrow epTy bndTy)) ep bnd) = do
  unless (epTy == ep) $
    coreErr [DS "AInd ep"]
  aKcAt Logic (AArrow epTy bndTy)
  ((y, unembed -> aTy), bTy) <- unbind bndTy
  ((f,dumby), dumbb) <- unbind bnd
  let b = subst dumby (AVar y) dumbb
  when (ep == Erased) $ do
    bIsVal <- isEValue <$> erase b
    unless bIsVal $
      coreErr [DS "ARec Erased nonvalue"]
    runtimeVars <- fv <$> erase b
    when (translate y `S.member` runtimeVars) $
      coreErr [DS "ARec Erased var"]
  (th',  bTy') <-
    extendCtx (ASig y Logic aTy) $
      extendCtx (ASig f Logic (AArrow epTy bndTy)) $
        aTs b
  bTyEq <- aeq <$> erase bTy <*> erase bTy'
  unless bTyEq $
    coreErr [DS "ARec annotation mismatch"]
  return $ (Program, AArrow epTy bndTy)
  
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
  aKcAny bTy  --To check that no variables escape.
  return (max th th', bTy) --The max enforces that P vars can not be bound in an L context.

aTs (ACase a bnd ty) = do
  (xeq, mtchs) <- unbind bnd
  (th, aTy) <- aTs a
  case aTy of 
    (ATCon c idxs) -> do
      tCon <- lookupTCon c
      case tCon of 
        (delta, _, _, Just cons) -> do
          unless (length mtchs == length cons) $
            coreErr [DS "ACase The case expression has", DD (length mtchs),
                     DS "branches, but the datatype", DD c, DS "has", DD (length cons), DS "constructors"]
          unless (length delta == length idxs) $
            coreErr [DS "ACase malformed core term, this should never happen"]
          ths <- mapM (aTsMatch th ty (zip (map (\(x,_,_)->x) delta) idxs) cons (\pat -> ASig xeq Logic (ATyEq a pat)))
                      mtchs
          return (max th (maximum (minBound:ths)), ty)     
        (_, _, _, Nothing) -> coreErr [DS "ACase case on abstract type"]
    _ -> coreErr [DS "ACase not data"]

aTs (ATrustMe ty) = do
  th <- aKc ty
  return (th, ty)

aTs (ASubstitutedFor a _) = aTs a

-- Compute the best theta that can be given to a term.
aGetTh :: ATerm -> TcMonad Theta
aGetTh a = do
  (th, _) <- aTs a
  return th

-- Check that a term is a type (at any theta)
aKcAny :: ATerm  -> TcMonad ()
aKcAny t  = aKc t >> return ()

-- Check that a term is a type (at a given theta)
aKcAt :: Theta -> ATerm -> TcMonad ()
aKcAt th t  = do
  th' <- aKc t
  if th' <= th 
    then return ()
    else coreErr [DS "The type", DD t, DS "should check at L but checks at P"]

-- Check that a term is a type 
aKc :: ATerm  -> TcMonad Theta
aKc t  = do
  (th,ty) <- aTs t
  ety <- erase ty
  case ety of
    (EType _) -> return th
    _ -> coreErr [DD t, DS "should be a type, but has type", DD ty]

-- Check that all types in a telescope are well-formed.
aKcTele :: ATelescope -> TcMonad Theta
aKcTele [] = return Logic
aKcTele ((x,ty,ep):rest) = do
  th1 <- aKc ty
  th2 <- extendCtx (ASig x th1 ty) $ aKcTele rest
  return (max th1 th2)

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
      unless (length cargs == length xs) $
        coreErr [DS "AMatch: Branch expects", DD (length xs), DS "arguments",
                 DS "but the constructor", DD c, DS "has", DD (length cargs), DS "arguments"]
      extendCtxTele (aSwapTeleVars (substs idxs cargs) (map fst xs)) th $ 
        extendCtx (xeq (ADCon c (map snd idxs) (map (\(x,ep) -> (AVar x, ep)) xs))) $ do
         (th', ty') <- aTs a
         ety' <- erase ty'
         ety  <- erase ty
         unless (ety' `aeq` ety) $
           coreErr [DS "AMatch: Branch has type", DD ty', DS "but was expected to have type", DD ty]
         return th'


aTcTele :: [(ATerm,Epsilon)] -> ATelescope -> TcMonad Theta
aTcTele [] [] = return Logic
aTcTele ((t,ep1):ts) ((x,ty,ep2):tele') = do
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

isEFirstOrder :: ETerm -> TcMonad Bool
isEFirstOrder m = isEFirstOrder' S.empty m
  where isEFirstOrder' :: Set EName -> ETerm -> TcMonad Bool
        isEFirstOrder' _ (ETyEq _ _)    = return True
        isEFirstOrder' _ (ESmaller _ _) = return True
        isEFirstOrder' _ (EAt _ _)      = return True
        isEFirstOrder' s (ETCon d _) | d `S.member` s  = return True
        isEFirstOrder' s (ETCon d _) = do
           ent <- lookupTCon (translate d)
           case ent of 
             (_,_,_,Nothing)   -> return False --Abstract datatype constructor
             (_,_,_,Just cons) -> --see corresponding comment in TypeCheck.hs
               allM (\(AConstructorDef _ args) ->
                         allM (\(_,ty,_) -> do
                                           ety <- erase ty
                                           isEFirstOrder' (S.insert d s) ety)
                              args)
                    cons
        isEFirstOrder' _ _ = return False
             
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
  aKcAt th aTy
  extendCtx d $ aTcEntries rest
aTcEntries (d@(ADef x a) : rest) = do
  _ <- aTs a
  extendCtx d $ aTcEntries rest
aTcEntries (d@(AData t delta th lvl constructors) : rest) = do
  th1 <- aKcTele delta
  ths <- extendCtx (AAbsData t delta th lvl) $
            mapM (\(AConstructorDef c args) -> extendCtxTele delta th1 $ aKcTele args) constructors
  unless (th <= (max th1 (maximum (Logic:ths)))) $
    err [DS "Datatype", DD t, DS "was annotated at", DD th, DS "but only checks at P"]
  extendCtx d $ aTcEntries rest
aTcEntries (d@(AAbsData t delta th lvl) : rest)  = do 
  th1 <- aKcTele delta
  unless (th <= th1) $
    err [DS "Datatype", DD t, DS "was annotated at", DD th, DS "but only checks at P"]
