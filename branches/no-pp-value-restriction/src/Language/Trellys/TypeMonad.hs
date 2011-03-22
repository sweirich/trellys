{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction #-}
module Language.Trellys.TypeMonad where

import Language.Trellys.Error
import Language.Trellys.Environment

import Language.Trellys.GenericBind(FreshMT(..), runFreshMT)


import Control.Monad.Reader hiding (join)
import Control.Monad.State hiding (join)
import Control.Monad.Error hiding (join)

-- The Monad that we will be using includes reader (for the
-- environment), freshness state (for supporting locally-nameless
-- representations), and error (for error reporting.
type TcMonad = FreshMT (ReaderT Env (ErrorT Err IO))

runTcMonad :: Env -> TcMonad a -> IO (Either Err a)
runTcMonad env m = runErrorT $
             flip runReaderT env $
             runFreshMT m

instance MonadReader Env TcMonad where
  ask = FreshMT ask
  local f (FreshMT a) = FreshMT (local f a)

instance MonadError Err TcMonad where
  throwError = FreshMT . throwError
  catchError m handler = FreshMT $ unFreshMT m `catchError` (\e -> unFreshMT (handler e))
