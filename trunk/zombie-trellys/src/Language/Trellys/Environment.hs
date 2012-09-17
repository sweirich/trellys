{-# LANGUAGE NamedFieldPuns, FlexibleContexts #-}

-- | Utilities for managing a typechecking context.
module Language.Trellys.Environment
  (
   Env,
   getFlag,
   emptyEnv, dumpEnv,
   lookupTy, lookupDef, lookupHint, lookupTCon, lookupDCon, getTys,
   getCtx, extendCtx, extendCtxTele, extendCtxs,
   extendCtxMods,
   extendHints,
   extendSourceLocation, getSourceLocation,
   substDefs,
   err, warn
  ) where

import Language.Trellys.Options
import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint
import Language.Trellys.Error

import Language.Trellys.GenericBind

import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos(SourcePos)
import Control.Monad.Reader
import Control.Monad.Error

import Data.List
import Data.Maybe (listToMaybe, catMaybes)

-- | Environment manipulation and accessing functions
-- The context 'gamma' is a list
data Env = Env { ctx :: [Decl], 
               -- ^ This context has both the type declarations and the
               -- definitions, for convenience
                 hints :: [Decl],
               -- ^ Type declarations (signatures): it's not safe to
               -- put these in the context until a corresponding term
               -- has been checked.
                 flags :: [Flag],
               -- ^ Command-line options that might influence typechecking
                 sourceLocation ::  [SourceLocation]
               -- ^ what part of the file we are in (for errors/warnings)
               } 
  --deriving Show


-- | The initial environment.
emptyEnv :: [Flag] -> Env
emptyEnv fs = Env { ctx = [] , hints = [], flags = fs, sourceLocation = [] }

instance Disp Env where
  disp e = vcat [disp decl | decl <- ctx e]

-- | Determine if a flag is set
getFlag :: (MonadReader Env m) => Flag -> m Bool
getFlag f = do 
 flags <- asks flags
 return (f `elem` flags)

-- return a list of all type bindings, and their names.
getTys :: (MonadReader Env m) => m [(TName,Theta,Term)]
getTys = do
  ctx <- asks ctx
  return $ catMaybes (map unwrap ctx)
    where unwrap (Axiom v th ty) = Just (v,th,ty)
          unwrap (Sig   v th ty) = Just (v,th,ty)
          unwrap _ = Nothing

-- | Find a name's user supplied type signature.
lookupHint   :: (MonadReader Env m) => TName -> m (Maybe (Theta,Term))
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [(th,ty) | Sig v' th ty <- hints, v == v']

-- | Find a name's type in the context.
lookupTy :: (MonadReader Env m, MonadError Err m, MonadIO m) 
         => TName -> m (Maybe (Theta,Term))
lookupTy v = do
  ctx <- asks ctx
  return $ listToMaybe (   [(th,ty) | Sig   v' th ty <- ctx, v == v'] 
                        ++ [(th,ty) | Axiom v' th ty <- ctx, v == v'])

-- | Find a name's def in the context.
lookupDef :: (MonadReader Env m, MonadError Err m, MonadIO m) 
          => TName -> m (Maybe Term)
lookupDef v = do
  ctx <- asks ctx
  return $ listToMaybe [a | Def v' a <- ctx, v == v']

-- | Find a type constructor in the context
lookupTCon :: (MonadReader Env m, MonadError Err m) 
          => TName -> m (Telescope,Theta,Integer,Maybe [ConstructorDef])
lookupTCon v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = err [DS "The type constructor", DD v, DS "was not found."]
    scanGamma ((Data v' delta th lev cs):g) = 
      if v == v' 
        then return $ (delta,th,lev,Just cs) 
        else  scanGamma g
    scanGamma ((AbsData v' delta th lev):g) =
      if v == v'
         then return $ (delta,th,lev,Nothing)
         else scanGamma g
    scanGamma (_:g) = scanGamma g

-- | Find a data constructor in the context
lookupDCon :: (MonadReader Env m, MonadError Err m) 
          => TName -> m (TName,Telescope,Theta,ConstructorDef)
lookupDCon v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = err [DS "The data constructor", DD v, DS "was not found."]
    scanGamma ((Data v' delta th lev cs):g) = 
        case find (\(ConstructorDef _ v'' tele) -> v''==v ) cs of
          Nothing -> scanGamma g
          Just c -> return $ (v', delta, th, c)
    scanGamma ((AbsData v' delta th lev):g) = scanGamma g
    scanGamma (_:g) = scanGamma g

-- | Extend the context with a new binding.
extendCtx :: (MonadReader Env m) => Decl -> m a -> m a
extendCtx d =
  local (\ m@(Env {ctx = cs}) -> m { ctx = d:cs })

-- | Extend the context with a list of bindings
extendCtxs :: (MonadReader Env m) => [Decl] -> m a -> m a
extendCtxs ds = 
  local (\ m@(Env {ctx = cs}) -> m { ctx = ds ++ cs })

-- | Extend the context with a telescope
extendCtxTele :: (MonadReader Env m) => Telescope -> Theta -> m a -> m a
extendCtxTele bds th m = 
  foldr (\(x,tm,_) -> extendCtx (Sig x th tm)) m bds

-- | Extend the context with a module
extendCtxMod :: (MonadReader Env m) => Module -> m a -> m a
extendCtxMod mod k = extendCtxs (reverse (moduleEntries mod)) k -- Note we must reverse the order.

-- | Extend the context with a list of modules
extendCtxMods :: (MonadReader Env m) => [Module] -> m a -> m a
extendCtxMods mods k = foldr extendCtxMod k mods


-- | Get the complete current context
getCtx :: MonadReader Env m => m [Decl]
getCtx = asks ctx

-- | Push a new source position on the location stack.
extendSourceLocation :: (MonadReader Env m, Disp t) => SourcePos -> t -> m a -> m a
extendSourceLocation p t = 
  local (\ e@(Env {sourceLocation = locs}) -> e {sourceLocation = (SourceLocation p t):locs})

getSourceLocation :: MonadReader Env m => m [SourceLocation]
getSourceLocation = asks sourceLocation

-- | Add a type hint
extendHints :: (MonadReader Env m) => Decl -> m a -> m a
extendHints h = local (\m@(Env {hints = hs}) -> m { hints = h:hs })

-- | substitute all of the defs through a term
substDefs :: MonadReader Env m => Term -> m Term
substDefs tm =
  let
    substDef :: Term -> Decl -> Term
    substDef m (Def nm df)         = subst nm df m
    substDef m (Sig _ _ _)         = m
    substDef m (Axiom _ _ _)         = m
    substDef m (Data _ _ _ _ _)    = m
    substDef m (AbsData _ _ _ _)   = m
  in
    do defs <- getCtx
       return $ foldl' substDef tm defs

-- | Print the context to a depth @n@.
dumpEnv :: (MonadReader Env m, MonadIO m) => Int -> m ()
dumpEnv n = do
  ctx <- asks ctx
  hints <- asks hints
  liftIO $ putStrLn "-- BENV --"
  liftIO $ putStrLn $ render $
         disp (Env {ctx = take n ctx, 
                    hints = take n hints, 
                    flags = [],
                    sourceLocation = []})
  liftIO $ putStrLn "-- EENV --"

-- Throw an error
err :: (Disp a,MonadError Err m, MonadReader Env m) => a -> m b
err d = do
  loc <- getSourceLocation
  throwError $ Err loc (disp d)

-- Print a warning
warn :: (Disp a, MonadReader Env m, MonadIO m) => a -> m ()
warn e = do
  loc <- getSourceLocation
  liftIO $ putStrLn $ "warning: " ++ render (disp (Err loc (disp e)))