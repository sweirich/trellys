{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts, TupleSections,
             ViewPatterns  #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | The operational semantics for Trellys core. This module currently has been
-- defined in just-in-time fashion, and should be replaced with an
-- implementation that systematically defines the operational semantics.
module Language.Trellys.OpSem
  (makeModuleEnv, join, isEValue, isValue, erase, eraseToHead, cbvStep, cbvNSteps)
where

import Language.Trellys.Options
import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint
import Language.Trellys.Environment
import Language.Trellys.TypeMonad
import Language.Trellys.GenericBind

import Control.Applicative 
import Control.Monad hiding (join)
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Generics.RepLib as RL

---------------------------------------------------------------
-- Erasing core terms. 
---------------------------------------------------------------
erase :: (Fresh m, Applicative m) => ATerm -> m ETerm
erase (AVar x) = return $ EVar (translate x)
erase (AUniVar x _) = return $ EUniVar (translate x)
erase (ACumul a i) = erase a
erase (AType i) = return $ EType i
erase (ATCon c indxs) = ETCon (translate c) <$> mapM erase indxs
erase (ADCon c _ indxs args) = EDCon (translate c) <$> mapM (erase . fst) (filter ((==Runtime) . snd) args)
erase (AArrow _ ex ep bnd) = do
  ((x, unembed -> a), b) <- unbind bnd
  EArrow ep <$> erase a <*> (bind (translate x) <$> erase b)
erase (ALam _ _ ep bnd) = do
  (x, body) <- unbind bnd
  if ep == Runtime
    then ELam  <$> (bind (translate x) <$> erase body)
    else EILam <$> erase body
erase (AApp Runtime a b ty) = EApp  <$> erase a <*> erase b
erase (AApp Erased a b ty)  = EIApp <$> erase a
erase (AAt a th) = EAt <$> erase a <*> pure th
erase (AUnboxVal a) = erase a
erase (ABox a th) = erase a
erase (AAbort _) = return EAbort
erase (ATyEq a b) = ETyEq <$> erase a <*> erase b
erase (AJoin a i b j) = return EJoin
erase (AConv a _ _ _) = erase a
erase (AContra a ty) = return EContra
erase (AInjDCon a i) = return EJoin
erase (ASmaller a b) = ESmaller <$> erase a <*> erase b
erase (AOrdAx _ _) = return EOrdAx
erase (AOrdTrans _ _) = return EOrdAx
erase (AInd _  ep bnd) = do
  ((f, y), r) <- unbind bnd
  if (ep == Runtime) 
   then EIndPlus <$> (bind (translate f, translate y) <$> erase r)
   else EIndMinus <$> (bind (translate f) <$> erase r)
erase (ARec _ ep bnd) = do
  ((f, y), r) <- unbind bnd
  if (ep == Runtime) 
   then ERecPlus <$> (bind (translate f, translate y) <$> erase r)
   else ERecMinus <$> (bind (translate f) <$> erase r)
erase (ALet ep bnd _) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  if ep == Runtime
    then ELet <$> erase a <*> (bind (translate x) <$> erase b)
    else erase b
erase (ACase a bnd _) = do
  (xeq, matchs) <- unbind bnd
  ECase <$> erase a <*> (mapM eraseMatch matchs)
erase (ADomEq _) = return EJoin
erase (ARanEq _ _) = return EJoin
erase (AAtEq _) = return EJoin
erase (ANthEq _ _) = return EJoin
erase (ATrustMe _) = return ETrustMe
erase (ASubstitutedFor a _) = erase a

eraseMatch  :: (Fresh m, Applicative m) => AMatch -> m EMatch
eraseMatch (AMatch c bnd) = do
  (args, b) <- unbind bnd
  EMatch  (translate c)
      <$> (bind <$> eraseTele args <*> erase b)

eraseTele :: (Fresh m, Applicative m) => ATelescope -> m [EName]
eraseTele AEmpty = return []
eraseTele (ACons (unrebind-> ((x,_,Runtime), tele))) = (translate x:) <$> eraseTele tele
eraseTele (ACons (unrebind-> ((x,_,Erased),  tele))) = eraseTele tele
eraseTele _ = error "Impossible, but GHC can't tell that the above pattern matches are comprehensive."

-- | Remove all completely-erased syntactic form, until we get to the first 
--   constructor which shows up in the erased version.

-- This does the wrong thing for erased lets. 
-- But I really don't want this to live in a monad, and the elaboration algorithm
-- does not introduce erased lets anywhere, so it should not be a problem.
eraseToHead :: ATerm -> ATerm
eraseToHead (ACumul a i) = eraseToHead a
eraseToHead (AUnboxVal a) = eraseToHead a
eraseToHead (ABox a th) = eraseToHead a
eraseToHead (AConv a _ _ _) = eraseToHead a
eraseToHead (ASubstitutedFor a _) = eraseToHead a
eraseToHead a = a

-- Tries to undo the effect of substDefs. This is slow, but it's only
-- called when printing the error message for join failure.
unsubstDefsWith :: (Map ETerm EName) -> ETerm -> ETerm
unsubstDefsWith invdefs = RL.everywhere (RL.mkT unsubstDefsOnce)
  where unsubstDefsOnce m =
          case M.lookup m invdefs of
            Just x  -> EVar x
            Nothing -> m           

getInvDefs :: TcMonad (Map ETerm EName)
getInvDefs = do
  defs <- getDefs
  M.fromList <$> (mapM (\(x,a) -> (,) <$> erase a <*> pure (translate x)) defs)

-- | Checks if two terms have a common reduct within n full steps
join :: Int -> Int -> ETerm -> ETerm -> TcMonad Bool
join s1 s2 m n = do
  useParallelReduction <- getFlag UseParallelReduction
  let nsteps = if useParallelReduction then parNSteps else cbvNSteps
  m' <- nsteps s1 m
  n' <- nsteps s2 n
  let joined = m' `aeq` n'
  unless joined $ do
    invDefs <- getInvDefs
    warn [DS "Join failure:",
          DD m, DS ("reduces in "++show s1++" steps to"), 
          DD (unsubstDefsWith invDefs m'),
          DS "and",
          DD n, DS ("reduces in "++show s2++" steps to"), 
          DD (unsubstDefsWith invDefs n')]
  return joined

-- | Small-step semantics.
-- Returns Nothing when the argument cannot reduce 
cbvStep :: ETerm -> TcMonad (Maybe ETerm)
cbvStep (EVar _)         = return Nothing
cbvStep (EUniVar _)      = return Nothing
cbvStep (ETCon c idxs)   = return Nothing
cbvStep (EDCon c args)   = stepArgs [] args
  where stepArgs _       []         = return Nothing
        stepArgs prefix (a:as) = do
          stpa <- cbvStep a
          case stpa of
            Nothing -> stepArgs (a:prefix) as
            Just EAbort -> return $ Just EAbort
            Just a'     -> return $ Just (EDCon c (reverse prefix ++ a' : as))
cbvStep (EType _)        = return Nothing
cbvStep (EArrow _ _ _)   = return Nothing 
cbvStep (ELam _)         = return Nothing
cbvStep (EILam _)        = return Nothing
cbvStep (EApp a b)       =
  do stpa <- cbvStep a
     case stpa of
       Just EAbort -> return $ Just EAbort
       Just a'     -> return $ Just $ EApp a' b
       Nothing     ->
         if not (isEValue a) then return Nothing
           else do
             stpb <- cbvStep b
             case stpb of
               Just EAbort -> return $ Just EAbort
               Just b'     -> return $ Just $ EApp a b'
               Nothing     ->
         -- These lines are necessary for correctness, but temporarily 
         -- commented out since they break most unit tests...:
                 -- if (isEValue b) then
                   case a of
                     ELam bnd ->
                       do (x,body) <- unbind bnd
                          return $ Just $ subst x b body
                     ERecPlus bnd ->
                       do ((f,x),body) <- unbind bnd
                          return $ Just $ subst f a $ subst x b body
                     EIndPlus bnd ->
                       do ((f,x),body) <- unbind bnd
                          x' <- fresh (string2Name "x")
                          return $ Just $ subst f (ELam (bind x' (EILam (EApp a (EVar x'))))) $ subst x b body
                     _ -> return  Nothing
                  -- else return Nothing
cbvStep (EIApp a) =
  do stpa <- cbvStep a
     case stpa of 
       Just EAbort -> return $ Just EAbort
       Just a'     -> return $ Just $ EIApp a'
       Nothing     ->        
         case a of
           EILam body -> return $ Just $  body
           ERecMinus bnd ->
             do (f,body) <- unbind bnd
                return $ Just $ subst f a $ body
           EIndMinus bnd ->
             do (f,body) <- unbind bnd
                return $ Just $ subst f (EILam (EILam (EIApp a))) $ body
           _ -> do --warn [DS "The argument to EIApp does not step, it was", DD a]
                   return  Nothing
cbvStep (ETyEq _ _)     = return Nothing
cbvStep EJoin           = return Nothing
cbvStep EAbort          = return $ Just EAbort
cbvStep EContra         = return Nothing
cbvStep (ERecPlus _)    = return Nothing
cbvStep (ERecMinus _)  = return Nothing
cbvStep (EIndPlus _)    = return Nothing
cbvStep (EIndMinus _)  = return Nothing
cbvStep (ECase b mtchs) =
  do stpb <- cbvStep b
     case stpb of
       Just EAbort -> return $ Just EAbort
       Just b'     -> return $ Just $ ECase b' mtchs
       Nothing     ->
         case b of
           (EDCon c tms) ->
             case find (\(EMatch c' _) -> c' == c) mtchs of
               Nothing  -> return Nothing
               Just (EMatch c' bnd) ->
                 do (delta,mtchbody) <- unbind bnd
                    if (length delta /= length tms) then return Nothing
                      else return $ Just $ substs (zip delta tms) mtchbody
           _ -> return Nothing
cbvStep (ESmaller _ _) = return Nothing
cbvStep EOrdAx = return Nothing
--cbvStep (ETerminationCase _ _) = err [DS "Tried to excute a termination-case"]
cbvStep (ELet m bnd)   =
  do stpm <- cbvStep m
     case stpm of
       Just EAbort -> return $ Just EAbort
       Just m'     -> return $ Just $ ELet m' bnd
       Nothing -> 
            if not (isEValue m) 
              then return Nothing
              else do (x,n) <- unbind bnd
                      return $ Just $ subst x m n
cbvStep (EAt _ _) = return Nothing
cbvStep ETrustMe = return Nothing

-- takes up to n steps
cbvNSteps :: Int -> ETerm -> TcMonad ETerm
cbvNSteps n tm =
  if n == 0 then return tm else
    do stptm <- cbvStep tm
       case stptm of
         Nothing -> return tm
         Just tm' -> cbvNSteps (n - 1) tm'

-- | Parallel-reduction small-step semantics.
-- 
-- This reduces zero or more redexes inside a term. 
-- As is standard for parallel reduction relations, it does not try
--  to find further redexes in the subterms of a redex.
--
-- Unlike a standard parallel recuction relation, once it goes under a
-- binder it only reduces lambdas and case-expressions, not ind
-- expressions.  This decreases the risk of unfolding a term
-- indefinitely.  The boolean argument tracks whether we are under a
-- binder, when deep==True we don't unfold ind/rec.
--
parStep :: Bool -> ETerm -> TcMonad ETerm
parStep deep a@(EVar _)       = return a
parStep deep a@(EUniVar _)    = return a
parStep deep (ETCon c idxs)   = ETCon c <$> mapM (parStep deep) idxs
parStep deep (EDCon c args)   = EDCon c <$> mapM (parStep deep) args
parStep deep a@(EType _)      = return a
parStep deep (EArrow ep a bnd) = do
  (x,b) <- unbind bnd
  EArrow ep <$> (parStep True a) <*> (bind x <$> parStep True b)
parStep deep (ELam bnd)       = do
  (x,b) <- unbind bnd
  ELam <$> (bind x <$> parStep True b)
parStep deep (EILam b)         = EILam <$> parStep True b
parStep deep (EApp EAbort _)   = return EAbort
-- Note: for correctness, need a value restriction on b here,
--  and in the corresponding cases for RecPlus and IndPlus
parStep deep  (EApp (ELam bnd) b) = do
  (x,body) <- unbind bnd
  return $ subst x b body
parStep False (EApp a@(ERecPlus bnd) b) = do
  ((f,x),body) <- unbind bnd
  return $ subst f a $ subst x b body
parStep False (EApp a@(EIndPlus bnd) b) = do
  ((f,x),body) <- unbind bnd
  x' <- fresh (string2Name "x")
  return $ subst f (ELam (bind x' (EILam (EApp a (EVar x'))))) $ subst x b body
parStep deep (EApp a b) = EApp <$> parStep deep a <*> parStep deep b
parStep deep  (EIApp (EILam body)) = return body
parStep False (EIApp a@(ERecMinus bnd)) = do
  (f,body) <- unbind bnd
  return $ subst f a $ body
parStep False (EIApp a@(EIndMinus bnd)) = do
   (f,body) <- unbind bnd
   return $ subst f (EILam (EILam (EIApp a))) $ body
parStep deep (EIApp a) = EIApp <$> parStep deep a
parStep deep (ETyEq a b)     = ETyEq <$> parStep deep a <*> parStep deep b
parStep deep a@EJoin         = return a
parStep deep a@EAbort        = return a 
parStep deep a@EContra       = return a
parStep deep (ERecPlus bnd)  = do
  ((f,x), b) <- unbind bnd
  ERecPlus <$> (bind (f,x) <$> parStep True b)
parStep deep (ERecMinus bnd)  = do
  (f,b) <- unbind bnd
  ERecMinus <$> (bind f <$> parStep True b)
parStep deep (EIndPlus bnd)    = do
  ((f,x), b) <- unbind bnd
  EIndPlus <$> (bind (f,x) <$> parStep True b)
parStep deep (EIndMinus bnd)  = do
  (f,b) <- unbind bnd
  EIndMinus <$> (bind f <$> parStep True b)
parStep deep (ECase EAbort mtchs) = return EAbort
-- Todo: need a value-restriction for correctness.
parStep deep a@(ECase (EDCon c args) mtchs) = 
  case find (\(EMatch c' _) -> c' == c) mtchs of
    Nothing  -> return a  --This should probably never happen?
    Just (EMatch c' bnd) ->
        do (delta,mtchbody) <- unbind bnd
           if (length delta /= length args) 
             then return a
             else return $ substs (zip delta args) mtchbody
parStep deep (ECase a mtchs) = 
  ECase <$> parStep deep a <*> mapM parStepMatch mtchs
  where parStepMatch (EMatch c bnd) = do (xs,b) <- unbind bnd
                                         EMatch c <$> (bind xs <$> parStep True b)
parStep deep (ESmaller a b) = ESmaller <$> parStep deep a <*> parStep deep b
parStep deep a@EOrdAx = return a
parStep deep (ELet EAbort bnd) = return EAbort
parStep deep (ELet v bnd) | isEValue v = do
   (x,b) <- unbind bnd
   return $ subst x v b
parStep deep (ELet a bnd) = do
   (x,b) <- unbind bnd
   ELet <$> parStep deep a <*> (bind x <$> parStep True b)
parStep deep (EAt a th) = EAt <$> parStep deep a <*> pure th
parStep deep a@ETrustMe = return a

-- takes up to n steps
parNSteps :: Int -> ETerm -> TcMonad ETerm
parNSteps 0 a = return a
parNSteps n a = do 
 a' <- parStep False a 
 if (a `aeq` a')
  then return a 
  else parNSteps (n-1) a'

-- | isValue checks to see if a term is a value
-- This is  used in a single place in the entire program, wish I could get rid of it.
isValue :: (Fresh m, Applicative m) => Term -> m Bool
isValue (Var _)            = return True
isValue (UniVar _)         = return False
isValue (TCon _ args)      = return True
isValue (DCon _ args)      = allM (isValue . fst) args
isValue (Type _)           = return True
isValue (Arrow _ _ _)      = return True
isValue (Lam _ _)          = return True
isValue (App _ _ _)        = return False
isValue (Smaller _ _)      = return True
isValue (OrdAx _)          = return True
isValue (OrdTrans _ _)     = return True
isValue (TyEq _ _)         = return True
isValue (Join _ _)         = return True
isValue Abort              = return False
isValue (Ind ep _)         = return True
isValue (Rec ep _)         = return True
isValue (ComplexCase _)    = return False
isValue (Let _ Erased a) = do
  (_,a') <- unbind a 
  isValue a'
isValue (Let _ _ _)        = return False
isValue (Conv a _ _)       = isValue a
isValue (Contra _)         = return False
isValue (InjDCon _ _)      = return True
isValue (Ann a _)          = isValue a
isValue (Paren a)          = isValue a
isValue (Pos _ a)          = isValue a
isValue (At _ _)           = return True
isValue (TerminationCase _ _)     = return False
isValue TrustMe            = return True
isValue InferMe            = return False --Hm, dunno.
isValue (Unfold _ _ b)     = isValue b  --acts like erased let
isValue (SubstitutedFor  a _) = isValue a
isValue (SubstitutedForA a _) = isEValue <$> erase a

-- | checks if an erased term is a value.
isEValue :: ETerm -> Bool
isEValue (EVar _)         = True
isEValue (EUniVar _)      = False
isEValue (ETCon _ _)      = True
isEValue (EDCon _ args)   = all isEValue args
isEValue (EType _)        = True
isEValue (EArrow _ _ _)   = True
isEValue (ELam _)         = True
isEValue (EILam _)        = True
isEValue (EApp _ _)       = False
isEValue (EIApp _)        = False
isEValue (ESmaller _ _)   = True
isEValue EOrdAx           = True
isEValue (ETyEq _ _)      = True
isEValue EJoin            = True
isEValue EAbort           = False
isEValue (ERecPlus _)     = True
isEValue (ERecMinus _)    = True
isEValue (EIndPlus _)     = True
isEValue (EIndMinus _)    = True
isEValue (ECase _ _)      = False
isEValue (ELet _ _)       = False
isEValue EContra          = False
isEValue (EAt _ _)        = False
--isEValue (ETerminationCase _ _) = False
isEValue ETrustMe          = True

-- | Evaluation environments - a mapping between named values and
-- | their definitions.
type EEnv = [(TName,Term)]

-- | Convert a module into an evaluation environment (list of top level declarations)
makeModuleEnv :: Module -> EEnv
makeModuleEnv md = [(n,tm) | Def n tm <- moduleEntries md]
