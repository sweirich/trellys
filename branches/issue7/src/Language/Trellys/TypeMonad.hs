{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction #-}
module Language.Trellys.TypeMonad where

import Language.Trellys.Error
import Language.Trellys.Environment

import Language.Trellys.GenericBind(HasNext(..))


import Control.Monad.Reader hiding (join)
import Control.Monad.State hiding (join)
import Control.Monad.Error hiding (join)

-- The Monad that we will be using includes reader (for the environment), state
-- (for supporting locally-nameless representations), and error (for error
-- reporting.
type TcMonad = StateT Integer (ReaderT Env (ErrorT Err IO))

runTcMonad :: Env -> TcMonad a -> IO (Either Err a)
runTcMonad env m = runErrorT $
             flip runReaderT env $
             evalStateT m 0

instance HasNext TcMonad where
  nextInteger = do modify (+1)
                   get
  resetNext i = put i
