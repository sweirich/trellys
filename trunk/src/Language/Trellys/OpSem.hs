{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
-- | The operational semantics for Trellys core. This module currently has been
-- defined in just-in-time fashion, and should be replaced with an
-- implementation that systematically defines the operational semantics.
module Language.Trellys.OpSem
  (runEvalMonad,
   join, reduce,isValue, isEValue, eval, erase)
where


import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint
import Language.Trellys.Environment
import Language.Trellys.Error
import Language.Trellys.TypeMonad

import Language.Trellys.GenericBind

import Control.Monad hiding (join)
import Control.Monad.State hiding (join)
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)

import Data.Maybe

-- | erasure function
erase :: Term -> TcMonad ETerm
erase (Var x)               = return $ EVar (translate x)
erase (Con c)               = return $ ECon (translate c)
erase (Type l)              = return $ EType l
erase (Arrow th ep tyA bnd) =
  do (x, tyB) <- unbind bnd
     tyA' <- erase tyA
     tyB' <- erase tyB
     return $ EArrow th ep tyA' $ bind (translate x) tyB'
erase (Lam ep bnd)   =
  do (x,body) <- unbind bnd
     body' <- erase body
     if ep == Runtime
       then return $ ELam (bind (translate x) body')
       else return body'
erase (App Runtime a b) = liftM2 EApp (erase a) (erase b)
erase (App Erased  a _) = erase a
erase (TyEq a b)        = liftM2 ETyEq (erase a) (erase b)
erase (Join _ _)        = return EJoin
erase Abort             = return EAbort
erase (NatRec ep bnd)   =
  do ((f,x),body) <- unbind bnd
     body' <- erase body
     if ep == Runtime
       then return $ ERecPlus (bind (translate f, translate x) body')
       else return $ ERecMinus (bind (translate f) body')
erase (Rec ep bnd)      =
  do ((f,x),body) <- unbind bnd
     body' <- erase body
     if ep == Runtime
       then return $ ERecPlus (bind (translate f, translate x) body')
       else return $ ERecMinus (bind (translate f) body')
erase (Case a bnd)      =
  do a' <- erase a
     (_,mtchs) <- unbind bnd
     liftM (ECase a') (mapM eraseMatch mtchs)
erase (Let _ ep a bnd)       =
  do ((x,_),body) <- unbind bnd
     body' <- erase body
     case ep of
       Runtime -> do a' <- erase a
                     return $ ELet a' (bind (translate x) body')
       Erased  -> return body'
erase (Conv a _ _)      = erase a
erase (Contra _)        = return EContra
erase (Ann a _)         = erase a
erase (Paren a)         = erase a
erase (Pos _ a)         = erase a

eraseMatch :: Match -> TcMonad EMatch
eraseMatch (c,bnd) =
  do (xs,body) <- unbind bnd
     let xs' = map (translate . fst) $ filter (((==) Runtime) . snd) xs
     body' <- erase body
     return (translate c, bind xs' body')

-- | Checks if two terms have a common reduct within n full steps
join :: Int -> Int -> ETerm -> ETerm -> TcMonad Bool
join s1 s2 m n =
  do m' <- cbvNSteps s1 m
     n' <- cbvNSteps s2 n

     let joined = m' `aeq` n'

     unless joined $
       do liftIO $ putStr "Join failure:\n  "
          liftIO $ print $ disp  m
          liftIO $ putStr "reduces to\n  "
          liftIO $ print $ disp m'
          liftIO $ putStr "and\n  "
          liftIO $ print $ disp n
          liftIO $ putStr "reduces to\n  "
          liftIO $ print $ disp n'

     return joined

-- | reduce a term to a normal form.  FIXME: This uses the large-step 'eval'
-- semantics, so the parameter to limit depth is ignored for now.
reduce :: (MonadReader Env m, MonadError Err m)
       => Int -> Term -> m Term
reduce _ t = do
  vals <- getCtx
  -- We have to convert the Entry to a (Name,Term) pair
  let vals' = concatMap (\d -> case d of
                                 Def n tm -> [(n,tm)]
                                 _ -> [])
                        vals

  return $ runEvalMonad vals' (eval t)


-- | Small-step semantics.
cbvStep :: ETerm -> TcMonad (Maybe ETerm)
cbvStep (EVar _)         = return Nothing
cbvStep (ECon _)         = return Nothing
cbvStep (EType _)        = return Nothing
cbvStep (EArrow th ep a bnd) = do
  stpa <- cbvStep a
  case stpa of
    Just EAbort -> return $ Just EAbort
    Just a'     -> return $ Just $ EArrow th ep a' bnd
    Nothing     ->
      if not (isEValue a) then return Nothing
       else do 
         (x,b) <- unbind bnd
         stpb <- cbvStep b
         case stpb of
           Just EAbort -> return $ Just EAbort
           Just b'     -> return $ Just $ EArrow th ep a (bind x b')
           Nothing ->
             if isEValue b
               then return $ Just $ (EArrow th ep a (bind x b))
               else return Nothing           
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
                 case a of
                   ELam bnd ->
                     do (x,body) <- unbind bnd
                        return $ Just $ subst x b body
                   ERecPlus bnd ->
                     do ((f,x),body) <- unbind bnd
                        return $ Just $ subst f a $ subst x b body
                   _ -> return Nothing
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
         case splitEApp b of
           (ECon c,tms) ->
             case lookup c mtchs of
               Nothing  -> return Nothing
               Just bnd ->
                 do (delta,mtchbody) <- unbind bnd
                    if (length delta /= length tms) then return Nothing
                      else return $ Just $ substs delta tms mtchbody
           _ -> return Nothing
cbvStep (ELet m bnd)   =
  do stpm <- cbvStep m
     case stpm of
       Just EAbort -> return $ Just EAbort
       Just m'     -> return $ Just $ ELet m' bnd
       _ -> if not (isEValue m) then return Nothing else
              do (x,n) <- unbind bnd
                 return $ Just $ subst x m n

-- takes up to n steps
cbvNSteps :: Int -> ETerm -> TcMonad ETerm
cbvNSteps n tm =
  if n == 0 then return tm else
    do stptm <- cbvStep tm
       case stptm of
         Nothing -> return tm
         Just tm' -> cbvNSteps (n - 1) tm'

-- | isValue checks to see if a term is a value
isValue :: Term -> Bool
isValue (Var _)            = True
isValue (Con _)            = True
isValue (Type _)           = True
isValue (Arrow _ _ t1 b)  =
  let (_,t2) = unsafeUnBind b in
  isValue t1 && isValue t2
isValue (Lam _ _)          = True
isValue (App _ e1 e2)      =
  isValue e2 &&
  (let (hd,tms) = splitApp e1 in
     (isJust $ isCon hd) && all (isValue . fst) tms)
isValue (TyEq _ _)         = True
isValue (Join _ _)         = True
isValue Abort              = False
isValue (NatRec ep _)      = ep == Runtime
isValue (Rec ep _)         = ep == Runtime
isValue (Case _ _)         = False
isValue (Let _ Erased _ a) =
  let (_,a') = unsafeUnBind a in
    isValue a'
isValue (Let _ _ _ _)      = False
isValue (Conv a _ _)       = isValue a
isValue (Contra _)         = False
isValue (Ann a _)          = isValue a
isValue (Paren a)          = isValue a
isValue (Pos _ a)          = isValue a

isEValue :: ETerm -> Bool
isEValue (EVar _)         = True
isEValue (ECon _)         = True
isEValue (EType _)        = True
isEValue (EArrow _ _ t1 b) = 
  let (_,t2) = unsafeUnBind b in
   isEValue t1 && isEValue t2
isEValue (ELam _)         = True
isEValue (EApp e1 e2)     =
  isEValue e2 &&
  (let (c,tms) = splitEApp e1 in
     (isJust $ isECon c) && all isEValue tms)
isEValue (ETyEq _ _)      = True
isEValue EJoin            = True
isEValue EAbort           = False
isEValue (ERecPlus _)     = True
isEValue (ERecMinus _)    = False
isEValue (ECase _ _)      = False
isEValue (ELet _ _)       = False
isEValue EContra          = False

-- | Evaluation environments - a mapping between named values and
-- | their definitions.
type EEnv = [(TName,Term)]

-- | Convert a module into an evaluation environment (list of top level declarations)
--makeModuleEnv :: Module -> EEnv
--makeModuleEnv md = [(n,tm) | Val n tm <- moduleEntries md]

-- | A monad to implement evaluation.
newtype EvalMonad a = EvalMonad (ReaderT EEnv FreshM a)
      deriving (Monad, Fresh, MonadReader EEnv )

-- | Execute the EvalMonad
runEvalMonad :: EEnv -> EvalMonad t -> t
runEvalMonad env (EvalMonad m) = runFreshM (runReaderT m env)

-- Evaluation, directly
-- | Large-step evaluation semantics
eval :: (MonadReader [(TName, Term)] m, Fresh m) => Term -> m Term
eval (Paren t) = eval t
eval (Pos _ t) = eval t
eval (App Runtime e1 e2) = do
  e1' <- eval e1
  e2' <- eval e2
  case e1' of
    Lam Runtime binding -> do
     (n,body) <- unbind binding
     eval (subst n e2' body)
    -- If the result is anything else, then
    -- we simply evaluate the argument and
    -- reconstruct an application. This is used,
    -- for example, when evaluating constructors
    _ -> return $ App Runtime e1' e2'
eval (App Erased e1 _) = do
  e1' <- eval e1
  case e1' of
    Lam Erased binding -> do
      (_,body) <- unbind binding
      return body
    -- We drop the application, since it's an implicit argument
    _ -> return e1'


eval (Var x) = do
  env <- ask
  case lookup x env of
    Just (Pos _ t) ->  return t
    Just (Paren t) -> return t
    Just t -> return t
    Nothing ->
      -- Free variables should evaluate to themselves?
      return (Var x)
      -- fail $ "eval: no such variable in scope " ++ (show x)

eval (Case dis bnd) = do
  d' <- eval dis
  (_,alts) <- unbind bnd
  let (cons,args) = cname d' []
      Just bd = lookup cons alts
  (ns,altBody) <- unbind bd
  -- FIXME: What to do about the extra witness parameters?
  return $ sub (map fst ns) args altBody
  where cname (Pos _ t) acc = cname t acc
        cname (Paren t) acc = cname t acc
        cname (App _ x y) acc = cname x (y:acc)
        cname (Con v) acc = (v,acc)
        cname _ _ = error "case evaluation: cannot find the constructor name"
        sub (p:ps) (a:as) t = sub ps as $ subst p a t
        sub _ _ t = t

eval t
  | isValue t = return t
  | otherwise = fail $  "eval: unhandled term " ++ show t

