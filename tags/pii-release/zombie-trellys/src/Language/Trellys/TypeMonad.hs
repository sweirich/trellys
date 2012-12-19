{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction #-}
module Language.Trellys.TypeMonad where

import Language.Trellys.Error
import Language.Trellys.Environment

import Language.Trellys.GenericBind(FreshMT(..), runFreshMT)


import Control.Monad.Reader(ReaderT(..))
import Control.Monad.Writer(WriterT(..))
import Control.Monad.Error(ErrorT(..))


-- The Monad that we will be using includes reader (for the
-- environment), freshness state (for supporting locally-nameless
-- representations),  error (for error reporting), and IO (for e.g. 
-- warning messages).
type TcMonad = FreshMT ((ReaderT Env (ErrorT Err IO)))

runTcMonad :: Env -> TcMonad a -> IO (Either Err a)
runTcMonad env m = runErrorT $
             flip runReaderT env $
             runFreshMT m
