-- Note: need to do ":cd ../.." in *haskell* window to make things work.
-- Or if SCW then :cd /Users/sweirich/vc/gcode/trellys/zombie-trellys/src/

{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    UndecidableInstances, ViewPatterns, TupleSections #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

module Language.Trellys.TypeCheckCore (
  getType, aTcModules, aTs, aKc, aGetTh, 
  underCase, underInd, underRec, underLet,
  isEFirstOrder
) where

import Data.List (find)
import qualified Data.Set as S
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)
import Control.Applicative

import qualified Generics.RepLib as RL

import Language.Trellys.Diff
import Language.Trellys.Error
import Language.Trellys.Options
import Language.Trellys.Environment -- (Env, err, lookupTy, lookupTCon, lookupDCon, extendCtx)
import Language.Trellys.GenericBind
import Language.Trellys.Syntax
import Language.Trellys.OpSem (isEValue, erase, eraseToHead, join)
import Language.Trellys.TypeMonad

--Stuff used for debugging.
{-
import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ ( (<>), (<+>),hsep,text, parens, brackets, render)
-}

-------------------
-------------------
-- Just accessing the type of a core-language term
-------------------
-------------------

{-
  We maintain the following invariants wrt zonking:
    - The argument to getType is already zonked.
    - The values returned by getType are zonked before they are returned.
    - The types in the environment are not yet zonked.
-}

getType :: ATerm -> TcMonad (Theta, ATerm)

getType (AVar x) = do
  (th, ty) <- lookupTy x
  zty <- zonkTerm ty
  maybeUseFO (AVar x) (th,zty)

getType (AUniVar x ty) =  do 
  secondPass <- getFlag SecondPass
  if secondPass
    then coreErr [DS "Encountered an uninstantiated unification variable", DD x, DS "of type", DD ty]
    -- todo, the Logic is probably wrong, maybe need to do something smarter.
    else return (Logic,ty)
  
getType (ACumul a j) = return (Logic, AType j) 
                       -- should aTs require that cumul used only for logical types?
getType (AType i) = return (Logic, AType (i+1))                       
getType deriv@(AUnbox a) = do
  (_, atTy) <- getType a 
  case eraseToHead atTy of 
     (AAt ty th) -> return (th, ty)
     _  -> coreErr [DS "getType: argument of AUnbox should have an @-type, but has type", 
                    DD atTy,
                    DS ("\n in (" ++ show deriv ++ ")") ]
getType (ATCon c _) = do
  (_, i, _) <- lookupTCon c
  return (Logic, AType i)            

getType (ADCon c th idxs args) = do 
  (tyc, _, _) <- lookupDCon c 
  return (th, ATCon (translate tyc) idxs)

getType  (AArrow j ex ep bnd) = return (Logic, AType j)

getType (ALam th (eraseToHead -> (AArrow k ex epTy bndTy))  ep bnd) = 
  return (th, AArrow k ex epTy bndTy) 
  
getType (ALam _ _ _ _) = coreErr [DS "getType: Annotation type on ALam incorrect"]

getType (AApp ep a b ty) = do
  (tha, _) <- getType a
  (thb, _) <- getType b
  return (max tha thb, ty)

getType (AAt a th') = do
  (_,aTy) <- getType a
  case eraseToHead aTy of 
    AType i -> return $ (Logic, AType i)
    _ -> coreErr [DS "getType: The argument to AAt should be a type, but it is", DD a, DS "which has type", DD aTy]

  
-- maybe add type annotation here?  
getType (ABox a th') = do
  (th, aTy) <- getType a
  isVal <- isEValue <$> erase a
  case th of 
    Logic                  -> return (Logic, AAt aTy th')
    Program | isVal && th'==Program  -> return (Logic, AAt aTy th')
    Program | th'==Program -> return (Program, AAt aTy th')
    _ -> coreErr [DS "getType: In ABox,", DD a, DS "should check at L but checks at P"]
  
getType (AAbort aTy) =
  return (Program, aTy)

getType (ATyEq a b) = 
  return (Logic, AType 0)

getType (AJoin a _ b _ _) = 
  return (Logic, ATyEq a b)

getType (AConv a pf) = do
  (th, _) <- getType a
  (_, ATyEq _ ty) <- getType pf
  return (th, ty)

getType (ACong  _ _ ty) = do
  return (Logic, ty)
  
getType (AContra a ty) = do  
  return (Logic, ty)
  
getType (AInjDCon a i) = do
  (_,aTy) <- getType a
  case eraseToHead aTy of
     ATyEq (ADCon _ _ _ args) (ADCon _ _ _ args') ->
       return (Logic, ATyEq (fst (args !! i)) (fst (args' !! i)))
     _ -> coreErr [DS "getType AInjDCon: the term", DD a, 
                   DS"should prove an equality of datatype constructors, but it has type", DD aTy]


getType (ASmaller a b) = 
  return (Logic, AType 0)
    
getType (AOrdAx pf a1) = do
  (_,pfTy) <- getType pf
  case eraseToHead pfTy of            
    (ATyEq b1 _) -> return (Logic, ASmaller a1 b1)
    _ -> coreErr [DS "getType: AOrdAx badeq"]
    
getType (AOrdTrans a b) = do
  (_, tya) <- getType a
  (_, tyb) <- getType b
  case (eraseToHead tya, eraseToHead tyb) of
    (ASmaller t1 _, ASmaller _ t3') ->
       return $ (Logic, ASmaller t1 t3')
    _ -> coreErr [DS "getType: The subproofs of AOrdTrans do not prove inequalities of the right type."]

getType (AInd (eraseToHead -> (AArrow k ex epTy bndTy)) bnd) = 
  return (Logic, AArrow k ex epTy bndTy)

getType (AInd _ _) = coreErr [DS "getType: Annotation type on AInd incorrect"]

getType  (ARec (eraseToHead -> (AArrow k ex epTy bndTy)) bnd) =
  return (Program, AArrow k ex epTy bndTy)

getType (ARec _ _) = coreErr [DS "getType: Annotation type on ARec incorrect"]

getType (ALet ep bnd annot) = return annot

getType (ACase a bnd annot) = return annot

-- From (A->A')=(B->B'), conclude B=A. Note the built-in application of symmetry.
getType t@(ADomEq a) = do
  (th, aTy) <- aTs a
  case aTy of
    ATyEq (AArrow _ _ eps bndTy) (AArrow _ _ eps' bndTy') | eps == eps' ->
      unbind2 bndTy bndTy' >>=
        maybe (coreErr [DS "getType: ADomEq applied to incorrect equality type"])
              (\((_, unembed -> tyDom), _, (_, unembed -> tyDom'), _) ->
                return (th, ATyEq tyDom' tyDom))
    _ -> coreErr [DS "getType: ADomEq not applied to an equality between arrow types"]   

-- FIXME: this never gets around to checking that the types aTy and aTy' actually match the expected types.          
getType (ARanEq p a a') = do
  (th,  pTy) <- getType p
  (_, aTy) <- getType a
  (_, aTy') <- getType a'
  case pTy of
    ATyEq (AArrow _ _ eps bndTy) (AArrow _ _ eps' bndTy') | eps == eps' -> do
      unbindRes <- unbind2 bndTy bndTy'
      case unbindRes of
        Nothing -> coreErr [DS "getType: ARanEq incorrect equality type"]
        Just ((tyVar, unembed -> tyDom), tyRan, (_, unembed -> tyDom'), tyRan') -> do
          return (th, ATyEq (subst tyVar a tyRan) (subst tyVar a' tyRan'))
    _ -> coreErr [DS "getType: ARanEq not applied to an equality between arrow types"]

getType t@(AAtEq a) = do
  (th, aTy) <- getType a
  case aTy of
    ATyEq (AAt atTy th') (AAt atTy' th'') | th' == th'' -> return (th, ATyEq atTy atTy')
    _ -> coreErr [DS "getType: AAtEq not applied to an equality between at-types"]

getType (ANthEq i a) = do
  (th, aTy) <- getType a
  case aTy of
    ATyEq (ATCon c as) (ATCon c' as')
      | c /= c'                 -> coreErr [DS "ANthEq between different data types"]
      | length as /= length as' -> coreErr [DS "ANthEq between mismatched ATCon lengths"]
      | i < 0                  -> coreErr [DS "ANthEq at negative index"]
      | i >= length as           -> coreErr [DS "ANthEq index out of range"]
      | otherwise               -> return $ (th, ATyEq (as !! i) (as' !! i))
    _ -> coreErr [DS "getType: ANthEq not applied to an equality between type constructor applications"]
 
getType (ATrustMe ty) = do
  return (Logic, ty)

getType (AHighlight a) = getType a

getType (AReflEq a) = return (Logic, ATyEq a a)

getType (ASymEq a) = do
  (_, aTy) <- getType a
  case aTy of 
    ATyEq a1 a2 -> return (Logic, ATyEq a2 a1)
    _-> coreErr [DS "getType: ASymEq proof produced non-equation", DD aTy]

getType (ATransEq a b) = do
  (_, aTy) <- getType a
  (_, bTy) <- getType b
  case (aTy, bTy) of 
    (ATyEq a1 a2, ATyEq b1 b2) -> return (Logic, ATyEq a1 b2)
    _ -> coreErr [DS "getType: ATransEq proof produced non-equation", DD aTy, DD bTy]

getType (AEraseEq a) = getType a



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
--
-- In order to print more helpful error messages there are two mutually recursive
-- functions, aTs (which stores a breadcrumb trail of where we are)  and aTsPos (which does the real work).

aTs :: ATerm -> TcMonad (Theta, ATerm)
aTs a = extendSourceLocation Nothing a $ aTsPos a

aTsPos :: ATerm -> TcMonad (Theta, ATerm)
aTsPos (AVar x) = maybeUseFO (AVar x) =<< (lookupTy x)

aTsPos (AUniVar x ty) = do 
  secondPass <- getFlag SecondPass
  if secondPass
    then coreErr [DS "Encountered an uninstantiated unification variable", DD x, DS "of type", DD ty]
    -- todo, the Logic is probably wrong, maybe need to do something smarter.
    else return (Logic,ty)

aTsPos (ACumul a j) = do
 (th, aTy) <- aTs a
 ty <- erase aTy
 case ty of
   (EType i) | i <= j -> return $ (th,AType j)
   _ -> coreErr [DS "Subterm of ACulum should be a type but is", DD aTy]

aTsPos (AType i) = return $ (Logic, AType (i+1))

aTsPos deriv@(AUnbox a) = do
  isVal <- isEValue <$> erase a
  (aTh, atTy) <- aTs a
  case eraseToHead atTy of
    (AAt ty th) -> do aKc ty
                      case (isVal, aTh) of
                        (True,  _)   -> return (th,ty)      -- T_UnboxVal
                        (_, Logic)   -> return (th,ty)      -- T_UnboxL
                        (_, Program) -> return (Program,ty) -- T_UnboxP
    _  -> coreErr [DS "Argument of AUnbox should have an @-type, but has type", DD atTy,
                   DS ("\n when checking (" ++ show deriv ++ ")") ]

aTsPos (ATCon c idxs) = do
  (tys, i, _) <- lookupTCon c
  aTcTeleLogic (map (,Runtime) idxs) tys
  return (Logic, AType i)

aTsPos (ADCon c th' idxs args) = do 
  (tyc, indx_tys, (AConstructorDef _ arg_tys)) <- lookupDCon c 
  th <- aTcTele (map (,Runtime) idxs ++ args) (aAppendTele indx_tys arg_tys)
  unless (th <= th') $
    coreErr [DS "DataCon annotation ", DD th, DS "not <=", DD th']
  aKc (ATCon (translate tyc) idxs)
  return (th', ATCon (translate tyc) idxs)

aTsPos (AArrow k ex ep bnd) = do
  ((x, unembed -> a), b) <- unbind bnd
  fo <- isEFirstOrder <$> (erase a)
  unless fo $ do
    coreErr [DS "The domain of an arrow should be first-order, but here it is", DD a]
  tya <- aTsLogic a
  tyb <- extendCtx (ASig x Program a) $ aTsLogic b
  case (tya, tyb) of
    (AType i, AType j) | k == max i j -> return (Logic, AType k)
    (_, AType _) -> coreErr [DS "domain of an arrow should be a type, but here is", DD tya]
    (_, _) -> coreErr [DS "range of an arrow should be a type, but here is", DD tyb]

aTsPos (ALam th (eraseToHead -> (AArrow k ex epTy bndTy))  ep bnd) = do
  unless (epTy == ep) $
    coreErr [DS "ALam ep"]  
  aKc (AArrow k ex epTy bndTy)  
  Just ((x , unembed -> aTy), bTy , _, b) <- unbind2 bndTy bnd
  (th', bTy') <- extendCtx (ASig x Program aTy) $ do    
    aTs b
  unless (th' <= th) (coreErr [DS "ALam theta annotation mismtach."]) 
  bTyEq <- aeq <$> (erase bTy) <*> (erase bTy')
  unless bTyEq $ do
    bTyErased  <- erase bTy
    bTyErased' <- erase bTy'
    coreErr [DS "ALam annotation mismatch, function body was annotated as", DD bTyErased,
             DS "but checks at", DD bTyErased',
             DS "The full annotation was", DD (AArrow k ex epTy bndTy)]
  return $ (th, AArrow k ex epTy bndTy)

aTsPos (ALam _ ty _ _) = coreErr [DS "ALam malformed annotation, should be an arrow type but is", DD ty]

aTsPos (AApp ep a b ty) = do
  (tha, tyA) <- aTs a
  (thb, tyB) <- aTs b
  aKc ty
  case eraseToHead tyA of
    AArrow _ _ ep' bnd -> do
      unless (ep == ep') $
        coreErr [DS "AApp ep mismatch"]
      when (ep == Erased && thb == Program) $
        coreErr [DS "AApp: an erased argument must terminate, but", DD b, DS "checks at P"]        
      ((x, unembed -> tyB'), tyC) <- unbind bnd
      tyBEq <- aeq <$> erase tyB <*> erase tyB'
      unless tyBEq $
        coreErr [DS "AApp dom mismatch. Expected", DD tyB', DS "but found", DD tyB,
                 DS "In the application", DD (AApp ep a b ty),
                 DS "the term", DD a, DS "has type", DD tyA, DS "and",
                 DD b, DS "has type", DD tyB]
      tyEq <- aeq <$> erase ty <*> erase (subst x b tyC)
      unless tyEq $ 
        coreErr [DS "AApp annotation mismatch. Application has type", DD (subst x b tyC), 
                 DS "but was annotated as", DD ty]
      return (max tha thb, ty)
    _ -> coreErr [DS "AApp: The term being applied,", DD a, DS "should have an arrow type, but here has type", DD tyA]

aTsPos (AAt a th') = do
  aTy <- aTsLogic a
  case eraseToHead aTy of 
    AType i -> return $ (Logic, AType i)
    _ -> coreErr [DS "The argument to AAt should be a type, but it is", DD a, DS "which has type", DD aTy]

aTsPos (ABox a th') = do
  (th, aTy) <- aTs a
  isVal <- isEValue <$> erase a
  case th of 
    Logic                  -> return (Logic, AAt aTy th')
    Program | isVal        -> return (Logic, AAt aTy th')
    Program | th'==Program -> return (Program, AAt aTy th')
    _ -> coreErr [DS "in ABox,", DD a, DS "should check at L but checks at P"]

aTsPos (AAbort aTy) = do
  aKc aTy
  return (Program, aTy)

aTsPos (ATyEq a b) = do
  _ <- aTs a
  _ <- aTs b 
  return (Logic, AType 0)

aTsPos (AJoin a i b j strategy) = do
  aKc (ATyEq a b)
  aE <- erase a
  bE <- erase b  
  joinable <- join i j aE bE strategy
  unless joinable $
    coreErr [DS "AJoin: not joinable"]
  return (Logic, ATyEq a b)

aTsPos (AConv a pf) = do
  (th, aTy) <- aTs a
  pfTy <- aTsLogic pf
  (aTy1, aTy2) <- case eraseToHead pfTy of
                    ATyEq aTy1 aTy2 -> return (aTy1, aTy2)
                    _           -> coreErr [DD pf, DS "should be a proof of an equality, but has type",
                                            DD pfTy,
                                            DS "(when checking the conv expression", DD (AConv a pf), DS ")"]
  fromEq <- aeq <$> erase aTy <*> erase aTy1
  unless fromEq $
    coreErr [DS "AConv: the term", DD a, DS "has type", DD aTy,
             DS "but the proof term has type", DD pfTy,
             DS "(when checking the conv expression", DD (AConv a pf), DS ")"]
  maybeUseFO a (th, aTy2)

aTsPos (ACong prfs bnd ty@(ATyEq lhs rhs)) = do
  (xs, template) <- unbind bnd
  etemplate <- erase template
  unless (length xs == length prfs) $
    coreErr [DS "ACong length mismatch"]
  eqs <-  let processPrf pf = do
                            pfTy <- aTsLogic pf
                            case eraseToHead pfTy of
                              ATyEq a1 a2 -> return (a1, a2)
                              _           -> coreErr [DD pf, DS "should be a proof of an equality, but has type",
                                                      DD pfTy,
                                                      DS "(when checking the cong expression", DD (ACong prfs bnd ty), DS ")"]
           in mapM processPrf prfs
  let aTy1 = substs (zip xs (map fst eqs)) template
  let aTy2 = substs (zip xs (map snd eqs)) template
  eqTy1   <- aeq <$> erase lhs  <*> erase aTy1
  eqTy2   <- aeq <$> erase rhs  <*> erase aTy2
  unless eqTy1 $  do
    lhs_diffed <- diff lhs aTy1
    aTy1_diffed <- diff aTy1 lhs
    coreErr [DS "ACong: the cong-expression was annotated as", DD (ATyEq lhs_diffed rhs), 
             DS "but substituting the LHSs of the equations into the template creates the type", DD aTy1_diffed,
             DS "When synthesizing the type of", DD (ACong prfs bnd ty)]
  unless eqTy2 $ do
    rhs_diffed <- diff rhs aTy2
    aTy2_diffed <- diff aTy2 rhs
    coreErr [DS "ACong: the cong-expression was annotated as", DD (ATyEq lhs rhs_diffed), 
             DS "but substituting the RHSs of the equations into the template creates the type", DD aTy2_diffed,           
             DS "When synthesizing the type of", DD (ACong prfs bnd ty)]
  aKc ty
  return (Logic, ty)

aTsPos (ACong prfs bnd ty) = err [DS "ACong should be annotated with an equality type, but the annotation here is", DD ty]

-- Todo: This currently only considers head-forms of data
-- constructors, but for the annotated operational semantics, this
-- will need to consider headforms of all flavours of types?
-- Maybe it's ok to just consider those cases stuck, though.
aTsPos (AContra a ty) = do 
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
   
aTsPos (AInjDCon a i) = do
  aTy <- aTsLogic a
  case eraseToHead aTy of
     ATyEq (ADCon c _ _ args) (ADCon c' _ _ args') -> do
       unless (c == c') $
         coreErr [DS "AInjDCon: the term", DD a, 
                  DS "should prove an equality where both sides are headed by the same data constructor, but in ", DD aTy, DS "the constructors are not equal"]
       good   <- and <$> mapM isGoodArg args
       good'  <- and <$> mapM isGoodArg args'
       unless (good && good') $ 
         coreErr [DS "AInjDCon: not all constructor arguments in", DD aTy, DS "are values or logical expressions."]
       unless (length args == length args') $
         coreErr [DS "AInjDCon: the two sides of", DD aTy, DS "have different numbers of arguments"]
       unless (i < length args) $
         coreErr [DS "AInjDCon: the index", DD i, DS "is out of range"]
       return (Logic, ATyEq (fst (args !! i)) (fst (args' !! i)))
     _ -> coreErr [DS "AInjDCon: the term", DD a, 
                   DS"should prove an equality of datatype constructors, but it has type", DD aTy]
  where isGoodArg (arg,ep) = do
           (aTh, _) <- aTs arg
           argE <- erase arg
           return $ aTh==Logic || isEValue argE

aTsPos (ASmaller a b)  = do
  _ <- aTs a   
  _ <- aTs b
  return (Logic, AType 0)

aTsPos (AOrdAx pf a1) = do 
  pfTy <- aTsLogic pf
  _ <- aTs a1
  ea1 <- erase a1
  case eraseToHead pfTy of 
    (ATyEq b1 (ADCon _ c params b2s)) -> do
       eb1 <- erase b1 
       eb2s <- mapM (erase . fst) b2s
       unless (any (aeq ea1) eb2s) $
         coreErr [DS "The term", DD a1, DS "is not one of the subterms appearing in RHS of", DD pfTy]
       return $ (Logic, ASmaller a1 b1)
    _ -> coreErr [DS "AOrdAx badeq"]
        
aTsPos (AOrdTrans a b) = do
  tya <- aTsLogic a
  tyb <- aTsLogic b
  case (eraseToHead tya, eraseToHead tyb) of
    (ASmaller t1 t2, ASmaller t2' t3') | t2 `aeq` t2' ->
       return $ (Logic, ASmaller t1 t3')
    _ -> coreErr [DS "The subproofs of AOrdTrans do not prove inequalities of the right type."]

-- TODO: n-ary ind.
aTsPos t@(AInd ty@(eraseToHead -> (AArrow k ex epTy bndTy)) bnd) = do
  aKc ty
  ty' <- underInd t 
                  (\f ys body bodyTy -> do
                    runtimeVars <- fv <$> erase body
                    when (any (\(y,ep) -> ep==Erased && translate y `S.member` runtimeVars) 
                          ys) $
                      coreErr [DS "AInd Erased var"]
                    bodyTy' <- aTsLogic body
                    isEq <- aeq <$> erase bodyTy' <*> erase bodyTy'
                    unless isEq $
                      coreErr [DS "Body of AInd was annotated as", DD bodyTy, 
                               DS "but has type", DD bodyTy']
                    return ())
  return $ (Logic, ty)

aTsPos (AInd ty _) = coreErr [DS "AInd malformed annotation, should be an arrow type but is", DD ty]  

aTsPos t@(ARec ty@(eraseToHead -> (AArrow k ex epTy bndTy))  bnd) = do
  aKc ty
  underRec t
           (\f ys body bodyTy -> do
              runtimeVars <- fv <$> erase body
              when (any (\(y,ep) -> ep==Erased && translate y `S.member` runtimeVars) 
                    ys) $
                coreErr [DS "ARec Erased var"]
              (_,  bodyTy') <- aTs body
              isEq <- aeq <$> erase bodyTy' <*> erase bodyTy'
              unless isEq $
                coreErr [DS "Body of ARec was annotated as", DD bodyTy, 
                         DS "but has type", DD bodyTy']
              return ())
  return $ (Program, ty)
  
aTsPos (ARec ty _) = coreErr [DS "ARec malformed annotation, should be an arrow type but is", DD ty]  

aTsPos (ALet ep bnd (th, ty)) = do  
  ((_, _, unembed -> a), _) <- unbind bnd
  (th'',bTy) <-  underLet (ALet ep bnd (th,ty)) 
                           (\x x_eq body -> do
                              runtimeVars <- fv <$> erase body
                              when (ep == Erased && (translate x) `S.member` runtimeVars) $
                                coreErr [DS "ALet erased var"]
                              aTs body)
  aKc bTy  --To check that no variables escape
  th' <- aGetTh a
  when (th' == Program && ep == Erased) $
    coreErr [DS "the bound term in ALet is P, so it cannot be erased"]
  --The max enforces that P vars can not be bound in an L context.
  when (max th' th'' > th) $ coreErr [DS "Incorrect th annotation on ALet",
                                      DS "It was", DD th, 
                                      DS "but scrutinee is", DD th', 
                                      DS "and the body is", DD th'']
  return (th, bTy) 

aTsPos (ACase a bnd (th,ty)) = do
  ths <- underCase (ACase a bnd (th,ty))
                   (\c xs body -> do  
                      (th', ty') <- aTs body
                      ety' <- erase ty'
                      ety  <- erase ty
                      unless (ety' `aeq` ety) $
                         coreErr [DS "AMatch: Branch has type", DD ty', 
                                  DS "but was expected to have type", DD ty]
                      return th')
  aTh <- aGetTh a
  let th' = maximum (aTh:ths)
  unless (th' <= th) $
              coreErr $ [DS "ACase theta annotation incorrect.",
                       DS "The annotation was", DD th, 
                       DS "but computed to be", DD th', 
                       DS "from the scrutinee", DD aTh, 
                       DS "and the branches"] ++ (map DD ths)  
  return (th , ty)     

-- From (A->A')=(B->B'), conclude B=A. Note the built-in application of symmetry!
aTsPos (ADomEq a) = do
  (th, aTy) <- aTs a
  case aTy of
    ATyEq (AArrow _ _ eps bndTy) (AArrow _ _ eps' bndTy') | eps == eps' ->
      unbind2 bndTy bndTy' >>=
        maybe (coreErr [DS "ADomEq applied to incorrect equality type"])
              (\((_, unembed -> tyDom), _, (_, unembed -> tyDom'), _) ->
                return (th, ATyEq tyDom' tyDom))
    _ -> coreErr [DS "ADomEq not applied to an equality between arrow types"]

aTsPos (ARanEq p a a') = do
  (th,pTy) <- aTs p
  (_, aTy)  <- aTs a
  (_, aTy') <- aTs a'
  case pTy of
    ATyEq (AArrow _ _ eps bndTy) (AArrow _ _ eps' bndTy') | eps == eps' -> do
      unbindRes <- unbind2 bndTy bndTy'
      case unbindRes of
        Nothing -> coreErr [DS "ARanEq incorrect equality type"]
        Just ((tyVar, unembed -> tyDom), tyRan, (_, unembed -> tyDom'), tyRan') -> do
          asEq <- aeq <$> erase a <*> erase a'
          unless asEq $
            coreErr [DS "ARanEq: the erasures of", DD a, DS "and", DD a', DS "are not equal"]
          -- Check that the resulting arrow type is well-formed:
          _ <- aTs (subst tyVar a tyRan)
          _ <- aTs (subst tyVar a' tyRan')
          return (th, ATyEq (subst tyVar a tyRan) (subst tyVar a' tyRan'))
    _ -> coreErr [DS "ARanEq not applied to an equality between arrow types"]

aTsPos (AAtEq a) = do
  (th, aTy) <- aTs a
  case aTy of
    ATyEq (AAt atTy th') (AAt atTy' th'') | th' == th'' -> return (th, ATyEq atTy atTy')
    _ -> coreErr [DS "AAtEq not applied to an equality between at-types"]

aTsPos (ANthEq i a) = do
  (th, aTy) <- aTs a
  case aTy of
    ATyEq (ATCon c as) (ATCon c' as')
      | c /= c'                 -> coreErr [DS "ANthEq between different data types"]
      | length as /= length as' -> coreErr [DS "ANthEq between mismatched ATCon lengths"]
      | i < 0                  -> coreErr [DS "ANthEq at negative index"]
      | i >= length as           -> coreErr [DS "ANthEq index out of range"]
      | otherwise               -> return $ (th, ATyEq (as !! i) (as' !! i))
    _ -> coreErr [DS "ANthEq not applied to an equality between type constructor applications"]

aTsPos (ATrustMe ty) = do
  aKc ty
  return (Logic, ty)

aTsPos (AHighlight a) = aTs a

aTsPos (AReflEq a) = do
  _ <- aTs a
  return (Logic, ATyEq a a)

aTsPos (ASymEq a) = do
  aTy <- aTsLogic a
  case aTy of 
    ATyEq a1 a2 -> return (Logic, ATyEq a2 a1)
    _-> coreErr [DS "ASymEq proof produced non-equation", DD aTy]

aTsPos (ATransEq a b) = do
  aTy <- aTsLogic a
  bTy <- aTsLogic b
  case (aTy, bTy) of 
    (ATyEq a1 a2, ATyEq b1 b2) -> do
          isEq <- aeq <$> erase a2 <*> erase b1
          unless isEq $
            coreErr [DS "ATransEq: the erasures of", DD a2, DS "and", DD b1, DS "are not equal"]             
          return (Logic, ATyEq a1 b2)
    _ -> coreErr [DS "ATransEq proof produced non-equation", DD aTy, DD bTy]

aTsPos (AEraseEq a) = do
  aTy <- aTsLogic a
  case aTy of
    ATyEq _ _ -> return (Logic, aTy)
    _ -> coreErr [DS "AEraseEq: type should be an equation but is", DD aTy]


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
  (th, _) <- getType a
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

-- Take an ind expression and apply cont to the body
-- This function also checks that the number and epsilon of the variables
-- matches arrow type in the annotation.
-- The two ATerms given to the continuation is the body and the type the body should have.
underInd :: ATerm -> (AName -> [(AName,Epsilon)] -> ATerm -> ATerm -> TcMonad a) 
            -> TcMonad a
underInd (AInd funTy bnd) cont  = do
  ((f,ys), body) <- unbind bnd

  -- fTy accumulates the type of the recursive variable, difference-list style.
  let go fTy bodyTy [] = 
             coreErr [DS "An ind-expression must have at least one argument, but", 
                      DD (AInd funTy bnd), DS "has none"]
      go fTy (eraseToHead-> (AArrow k' ex' ep' bnd')) ((x,ep):xs) = do
        unless (ep'==ep) $
          coreErr [DS "Epsilon of annotation and rec-expression do not match",
                   DS "for variable", DD x]
        ((x', unembed->domTy), rngTy) <- unbind bnd'
        if null xs
         then do
                x0 <- fresh (string2Name "x")
                z0 <- fresh (string2Name "z")
                let fTyEnd =  
                        AArrow k' Explicit ep
                               (bind (x0, embed domTy)
                                 (AArrow k' Explicit Erased
                                   (bind (z0, embed (ASmaller (AVar x0) (AVar x)))
                                      (subst x' (AVar x0) rngTy))))
                extendCtx (ASig x Logic domTy) $
                  extendCtx (ASig f Logic (fTy fTyEnd)) $
                    cont f ys body (subst x' (AVar x) rngTy)
         else extendCtx (ASig x Logic domTy) $
                go (\rest -> fTy $ AArrow k' ex' ep (bind (x, embed domTy) rest))  
                   (subst x' (AVar x) rngTy) 
                   xs
      go _ _ (_ : _) = 
        coreErr [DS "The ind-expression", DD (ARec funTy bnd), 
                 DS ("has " ++ show (length ys) ++ " arguments"),
                 DS "but was ascribed the type", DD funTy]
    in
      go (\x->x) funTy ys


underInd _ fun = err [DS "internal error: underInd applied to non-ind expression"]

-- Take a rec expression and apply cont to the body
-- This function also checks that the number and epsilon of the variables
-- matches arrow type in the annotation.
-- The two ATerms given to the continuation is the body and the type the body should have.
underRec :: ATerm -> (AName -> [(AName,Epsilon)] -> ATerm -> ATerm -> TcMonad a)
            -> TcMonad a
underRec (ARec funTy bnd) cont = do
  ((f,ys), body) <- unbind bnd
  let go (eraseToHead-> (AArrow k' ex' ep' bnd')) ((x,ep):xs) = do
        unless (ep'==ep) $
          coreErr [DS "Epsilon of annotation and rec-expression do not match",
                   DS "for variable", DD x]
        ((x', unembed->domTy), rngTy) <- unbind bnd'
        extendCtx (ASig x Logic domTy) $
          go (subst x' (AVar x) rngTy) xs
      go _ (_ : _) = 
        coreErr [DS "The rec-expression", DD (ARec funTy bnd), 
                 DS ("has " ++ show (length ys) ++ " arguments"),
                 DS "but was ascribed the type", DD funTy]
      go bodyTy [] = 
             extendCtx (ASig f Logic funTy) $
               cont f ys body bodyTy
    in
      go funTy ys
underRec _ fun = err [DS "internal error: underRec called on non-rec expression."]


-- Take a case-expression, and apply fun to each case alternative.
underCase :: ATerm -> (AName -> ATelescope -> ATerm -> TcMonad a) -> TcMonad [a]
underCase (ACase a bnd (th,ty)) fun = do
  (xeq, mtchs) <- unbind bnd
  (aTh, aTy) <- aTs a
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
          mapM (underMatch th 
                           ty 
                           (zip (binders delta) idxs) 
                           cons 
                           (\pat -> ASig xeq Logic (ATyEq a pat))
                           fun)
                      mtchs 
        (_, _,  Nothing) -> coreErr [DS "ACase case on abstract type"]
    _ -> coreErr [DS "ACase not data"]
underCase _ fun = err [DS "internal error: underCase called on a non-case expression."]

-- Apply fun to the body of an AMatch
underMatch ::  Theta                -- the theta of the scrutinee
             -> ATerm             -- the type that the branch should check at.
             -> [(AName,ATerm)]   -- substitution for type indexes
             -> [AConstructorDef] -- the constructors of the datatype
             -> (ATerm -> ADecl)  -- the "scrutinee = pattern" equality, partially applied
             -> (AName -> ATelescope -> ATerm -> TcMonad a) --function to apply.
             -> AMatch            -- the branch to check
             -> TcMonad a
underMatch th ty idxs cons xeq fun (AMatch c bnd) = do
  (xs, a) <- unbind bnd
  case find (\(AConstructorDef c' _) -> c'==c) cons of
    Nothing -> coreErr ([DS "AMatch: Trying to match against the constructor", DD c,
                         DS "which is not a constructor of the datatype.",
                         DS "The possible contructors that can be used are"] ++ map DD cons)
    Just (AConstructorDef _ cargs) -> do
      unless (aTeleLength cargs == aTeleLength xs) $
        coreErr [DS "AMatch: Branch expects", DD (aTeleLength xs), DS "arguments",
                 DS "but the constructor", DD c, DS "has", DD (aTeleLength cargs), DS "arguments"]
      tyEq <- eqTele xs (substs idxs cargs)
      unless tyEq $
        coreErr [DS "The pattern variables to the constructor", DD c, DS "were annotated to have types", DD xs,
                 DS "but should have types", DD (substs idxs cargs)]
      extendCtxTele xs th $ 
        extendCtx (xeq (ADCon c th (map snd idxs) (aTeleAsArgs xs))) $ 
          fun c xs a

-- Take a let-expression and apply fun to the body.
underLet :: ATerm -> (AName -> AName -> ATerm -> TcMonad a) -> TcMonad a
underLet (ALet ep bnd (th, ty)) fun = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  (th',aTy) <- aTs a
  when (th' == Program && ep == Erased) $
    coreErr [DS "the bound term in ALet is P, so it cannot be erased"]
  extendCtx (ASig x th' aTy) $ 
    extendCtx (ASig xeq Logic (ATyEq (AVar x) a)) $
      fun x xeq b
underLet _ fun = err [DS "internal error: underLet called on a non-let expression"]

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
  unless (ety' `aeq` ety) $ do
    ty_diffed <- diff ty ty'
    ty'_diffed <- diff ty' ty
    coreErr [DS "aTcTele: the expression",DD t,DS "should have type", DD ty_diffed,
             DS "but has type", DD ty'_diffed]
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
  unless (ety' `aeq` ety) $ do
    ty_diffed <- diff ty ty'
    ty'_diffed <- diff ty' ty
    coreErr [DS "aTcTeleLogic: the expression",DD t,
             DS "should have type", DD ty_diffed,
             DS "but has type", DD ty'_diffed]
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
  extendCtxsGlobal [d] $ aTcEntries rest
aTcEntries (d@(ADef x a) : rest) = do
  _ <- aTs a
  extendCtxsGlobal [d] $ aTcEntries rest
aTcEntries (d@(AData t delta lvl constructors) : rest) = do
  aKcTele delta
  extendCtx (AAbsData t delta lvl) $
            mapM_ (\(AConstructorDef c args) -> extendCtxTele delta Program $ aKcTele args) constructors
  mapM_ (aPositivityCheck t) constructors
  extendCtxsGlobal [d] $ aTcEntries rest
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
aOccursPositive x (AArrow _ _ _ bnd) = do
 ((_,unembed->tyA), tyB) <- unbind bnd
 when (x `S.member` (fv tyA)) $
    err [DD x, DS "occurs in non-positive position"]
 aOccursPositive x tyB
aOccursPositive x ty = do
  let children = RL.subtrees ty
  mapM_ (aOccursPositive x) children
