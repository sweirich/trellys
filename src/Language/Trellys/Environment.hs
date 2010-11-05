{-# LANGUAGE NamedFieldPuns, FlexibleContexts #-}

-- | Utilities for managing a typechecking context.
module Language.Trellys.Environment
  (
   Env,
   emptyEnv, dumpEnv,
   lookupVar, lookupVarDef, lookupCon, getDecls,
   extendEnv, extendEnvTele, extendEnvs, replaceEnv,
   substDefs
  )where

import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint
import Language.Trellys.Error

import Language.Trellys.GenericBind

import Text.PrettyPrint.HughesPJ
import Control.Monad.Reader
import Control.Monad.Error

import Data.List

-- | Environment manipulation and accessing functions
-- The context 'gamma' is a list
data Env = Env { decls :: [Decl] 
               -- ^ This context has both the type declarations and the
               -- definitions, for convenience
               } deriving Show


-- | The initial environment.
emptyEnv :: Env
emptyEnv = Env { decls = [] }

instance Disp Env where
  disp e = vcat [disp decl | decl <- decls e]

-- | Find a name's type in the context.
lookupVar :: (MonadReader Env m, MonadError Err m, MonadIO m) 
          => Name -> m (Theta,Term)
lookupVar v = do
  g <- asks decls
  scanGamma g
  where
    scanGamma [] = err [DS "The variable", DD v, DS "was not found."]
    scanGamma ((Sig v' th a):g) = 
      if v == v' then return (th,a) else scanGamma g
    scanGamma (_:g) = scanGamma g

-- | Find a name's def in the context.
lookupVarDef :: (MonadReader Env m, MonadError Err m, MonadIO m) 
             => Name -> m (Term)
lookupVarDef v = do
  g <- asks decls
  scanGamma g
  where
    scanGamma [] = err [DS "The variable", DD v, DS "was not found."]
    scanGamma ((Def v' a):g) = 
      if v == v' then return (a) else scanGamma g
    scanGamma (_:g) = scanGamma g

-- | Find a constructor in the context - left is type con, right is term con
lookupCon :: (MonadReader Env m, MonadError Err m) 
          => Name -> m (Either (Telescope,Theta,Int,Maybe [Constructor]) 
                               (Telescope,Theta,Term))
lookupCon v = do
  g <- asks decls
  scanGamma g
  where
    scanGamma [] = err [DS "The constructor", DD v, DS "was not found."]
    scanGamma ((Data v' delta th lev cs):g) = 
      if v == v' 
        then return $ Left (delta,th,lev,Just cs) 
        else case lookup v cs of
               Nothing -> scanGamma g
               Just tm -> return $ Right (delta, th, tm)
    scanGamma ((AbsData v' delta th lev):g) =
      if v == v'
         then return $ Left (delta,th,lev,Nothing)
         else scanGamma g
    scanGamma (_:g) = scanGamma g

-- | Extend the context with a new binding.
extendEnv :: (MonadReader Env m) => Decl -> m a -> m a
extendEnv d =
  local (\ m@(Env {decls = cs}) -> m { decls = d:cs })

-- | Extend the context with a list of bindings
extendEnvs :: (MonadReader Env m) => [Decl] -> m a -> m a
extendEnvs ds = 
  local (\ m@(Env {decls = cs}) -> m { decls = ds ++ cs })

-- | Extend the context with a telescope
extendEnvTele :: (MonadReader Env m) => Telescope -> m a -> m a
extendEnvTele bds m = 
  foldr (\(x,tm,th,_) -> extendEnv (Sig x th tm)) m bds

-- | Replace the entire context with a new one
replaceEnv :: (MonadReader Env m) => [Decl] -> m a -> m a
replaceEnv newenv = local (\_ -> Env newenv)

-- | Get the complete current context
getDecls :: MonadReader Env m => m [Decl]
getDecls = asks decls

-- | substitute all of the defs through a term
substDefs :: MonadReader Env m => Term -> m Term
substDefs tm =
  let
    substDef :: Term -> Decl -> Term
    substDef m (Def nm df)       = subst nm df m
    substDef m (Sig _ _ _)       = m
    substDef m (Data _ _ _ _ _)  = m
    substDef m (AbsData _ _ _ _) = m
  in
    do defs <- getDecls
       return $ foldl' substDef tm defs

-- | Print the context to a depth @n@.
dumpEnv :: (MonadReader Env m, MonadIO m) => Int -> m ()
dumpEnv n = do
  env <- asks decls
  liftIO $ putStrLn "-- BENV --"
  liftIO $ putStrLn $ render $ disp (Env (take n env))
  liftIO $ putStrLn "-- EENV --"
