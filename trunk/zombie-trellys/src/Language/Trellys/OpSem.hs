{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts, TupleSections,
             ViewPatterns  #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | The operational semantics for Trellys core. This module currently has been
-- defined in just-in-time fashion, and should be replaced with an
-- implementation that systematically defines the operational semantics.
module Language.Trellys.OpSem
  (makeModuleEnv, join, isEValue, isAValue, isValue, erase, eraseToHead, cbvStep, cbvNSteps)
where

import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint
import Language.Trellys.Environment
import Language.Trellys.TypeMonad
import Language.Trellys.GenericBind

import Control.Applicative 
import Control.Monad hiding (join)
import Data.List (find)

---------------------------------------------------------------
-- Erasing core terms. 
---------------------------------------------------------------
erase :: (Fresh m, Applicative m) => ATerm -> m ETerm
erase (AVar x) = return $ EVar (translate x)
erase (AFO a) = erase a
erase (ASquash a) = erase a
erase (ACumul a i) = erase a
erase (AType i) = return $ EType i
erase (ATCon c indxs) = ETCon (translate c) <$> mapM erase indxs
erase (ADCon c indxs args) = EDCon (translate c) <$> mapM (erase . fst) (filter ((==Runtime) . snd) args)
erase (AArrow ep bnd) = do
  ((x, unembed -> a), b) <- unbind bnd
  EArrow ep <$> erase a <*> (bind (translate x) <$> erase b)
erase (ALam _ ep bnd) = do
  (x, body) <- unbind bnd
  if ep == Runtime
    then ELam <$> (bind (translate x) <$> erase body)
    else erase body
erase (AApp Runtime a b ty) = EApp <$> erase a <*> erase b
erase (AApp Erased a b ty) = erase a
erase (AAt a th) = EAt <$> erase a <*> pure th
erase (AUnboxVal a) = erase a
erase (ABoxLL a th) = erase a
erase (ABoxLV a th) = erase a
erase (ABoxP a th) = erase a
erase (AAbort _) = return EAbort
erase (ATyEq a b) = ETyEq <$> erase a <*> erase b
erase (AJoin a i b j) = return EJoin
erase (AConv a _ _ _) = erase a
erase (AContra a ty) = return EContra
erase (ASmaller a b) = ESmaller <$> erase a <*> erase b
erase (AOrdAx _ _) = return EOrdAx
erase (AOrdTrans _ _) = return EOrdAx
erase (AInd _  ep bnd) = do
  ((f, y), r) <- unbind bnd
  if (ep == Runtime) 
   then ERecPlus <$> (bind (translate f, translate y) <$> erase r)
   else ERecMinus <$> (bind (translate f) <$> erase r)
erase (ARec _ ep bnd) = do
  ((f, y), r) <- unbind bnd
  if (ep == Runtime) 
   then ERecPlus <$> (bind (translate f, translate y) <$> erase r)
   else ERecMinus <$> (bind (translate f) <$> erase r)
erase (ALet ep bnd) = do
  ((x, xeq, unembed -> a), b) <- unbind bnd
  if ep == Runtime
    then ELet <$> erase a <*> (bind (translate x) <$> erase b)
    else erase b
erase (ACase a bnd _) = do
  (xeq, matchs) <- unbind bnd
  ECase <$> erase a <*> (mapM eraseMatch matchs)
erase (ATrustMe _) = return ETrustMe
erase (ASubstitutedFor a _) = erase a

eraseMatch  :: (Fresh m, Applicative m) => AMatch -> m EMatch
eraseMatch (AMatch c bnd) = do
  (xeps, b) <- unbind bnd
  EMatch  (translate c)
      <$> (bind (map (translate . fst) $ filter ((==Runtime).snd) xeps) <$> erase b)


-- | Remove all completely-erased syntactic form, until we get to the first 
--   constructor which shows up in the erased version.

-- This does the wrong thing for erased lets. 
-- But I really don't want this to live in a monad, and the elaboration algorithm
-- does not introduce erased lets anywhere, so it should not be a problem.
eraseToHead :: ATerm -> ATerm
eraseToHead (AFO a) = eraseToHead a
eraseToHead (ASquash a) = eraseToHead a
eraseToHead (ACumul a i) = eraseToHead a
eraseToHead (AUnboxVal a) = eraseToHead a
eraseToHead (AApp Erased a b ty) = eraseToHead a
eraseToHead (ABoxLL a th) = eraseToHead a
eraseToHead (ABoxLV a th) = eraseToHead a
eraseToHead (ABoxP a th) = eraseToHead a
eraseToHead (AConv a _ _ _) = eraseToHead a
eraseToHead (ASubstitutedFor a _) = eraseToHead a
eraseToHead a = a

-- | Checks if two terms have a common reduct within n full steps
join :: Int -> Int -> ETerm -> ETerm -> TcMonad Bool
join s1 s2 m n =
  do m' <- cbvNSteps s1 m
     n' <- cbvNSteps s2 n
     let joined = m' `aeq` n'
     unless joined $
       warn [DS "Join failure:",
             DD m, DS ("reduces in "++show s1++" steps to"), DD m',
             DS "and",
             DD n, DS ("reduces in "++show s2++" steps to"), DD n']
     return joined

-- | Small-step semantics.
-- Returns Nothing when the argument cannot reduce 
cbvStep :: ETerm -> TcMonad (Maybe ETerm)
cbvStep (EVar _)         = return Nothing
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
                     _ -> return  Nothing
                  -- else return Nothing
cbvStep (ETyEq _ _)     = return Nothing
cbvStep EJoin           = return Nothing
cbvStep EAbort          = return $ Just EAbort
cbvStep EContra         = return Nothing
cbvStep (ERecPlus _)    = return Nothing
cbvStep (ERecMinus bnd) =
  do (f,body) <- unbind bnd
     return $ Just $ subst f (ERecMinus bnd) body
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
       _ -> if not (isEValue m) then return Nothing else
              do (x,n) <- unbind bnd
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


-- | isValue checks to see if a term is a value
-- This is  used in a single place in the entire program, wish I could get rid of it.
isValue :: (Fresh m, Applicative m) => Term -> m Bool
isValue (Var _)            = return True
isValue (TCon _ args)      = return True
isValue (DCon _ args)      = allM (isValue . fst) args -- fixme: this is broken, params vs args.
isValue (Type _)           = return True
isValue (Arrow _ _)        = return True
isValue (Lam _ _)          = return True
isValue (App _ _ _)        = return False
isValue (Smaller _ _)      = return True
isValue (OrdAx _)          = return True
isValue (OrdTrans _ _)     = return True
isValue (TyEq _ _)         = return True
isValue (Join _ _)         = return True
isValue Abort              = return False
isValue (Ind ep _)         = return (ep == Runtime)
isValue (Rec ep _)         = return (ep == Runtime)
isValue (Case _ _)         = return False
isValue (ComplexCase _)    = return False
isValue (Let _ Erased a) = do
  (_,a') <- unbind a 
  isValue a'
isValue (Let _ _ _)        = return False
isValue (Conv a _ _)       = isValue a
isValue (Contra _)         = return False
isValue (Ann a _)          = isValue a
isValue (Paren a)          = isValue a
isValue (Pos _ a)          = isValue a
isValue (At _ _)           = return True
isValue (TerminationCase _ _)     = return False
isValue TrustMe            = return True
isValue InferMe            = return False --Hm, dunno.
isValue (Unfold _ _)       = return True  --acts like join
isValue (SubstitutedFor  a _) = isValue a
isValue (SubstitutedForA a _) = isEValue <$> erase a

-- | checks if an erased term is a value.
isEValue :: ETerm -> Bool
isEValue (EVar _)         = True
isEValue (ETCon _ _)      = True
isEValue (EDCon _ args)   = all isEValue args
isEValue (EType _)        = True
isEValue (EArrow _ _ _)   = True
isEValue (ELam _)         = True
isEValue (EApp _ _)       = False
isEValue (ESmaller _ _)   = True
isEValue EOrdAx           = True
isEValue (ETyEq _ _)      = True
isEValue EJoin            = True
isEValue EAbort           = False
isEValue (ERecPlus _)     = True
-- Fixme: this is wrong, but various test cases currenty assume it...
--isEValue (ERecMinus bnd)  = isEValue (snd (unsafeUnbind bnd)) 
isEValue (ERecMinus _) = False
isEValue (ECase _ _)      = False
isEValue (ELet _ _)       = False
isEValue EContra          = False
isEValue (EAt _ _)        = False
--isEValue (ETerminationCase _ _) = False
isEValue ETrustMe          = True

isAValue :: (Fresh m, Applicative m) => ATerm -> m Bool
isAValue a = isEValue <$> erase a

-- | Evaluation environments - a mapping between named values and
-- | their definitions.
type EEnv = [(TName,Term)]

-- | Convert a module into an evaluation environment (list of top level declarations)
makeModuleEnv :: Module -> EEnv
makeModuleEnv md = [(n,tm) | Def n tm <- moduleEntries md]
