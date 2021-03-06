{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction #-}
module Language.Trellys.TypeMonad where

import Unbound.LocallyNameless.Fresh
import Language.Trellys.Error
import Language.Trellys.Environment
import Language.Trellys.GenericBind(Fresh(..), Name)

import qualified Data.Map as M
import Control.Applicative
import Control.Monad (liftM)
import Control.Monad.RWS.Lazy
import Control.Monad.Fail
import Control.Monad.Error(ErrorT(..), throwError, strMsg)

-- The Monad that we will be using includes reader (for the
-- environment), freshness state (for supporting locally-nameless
-- representations), error (for error reporting), state (for the
-- bindings of unification variables) and IO (for e.g.  warning
-- messages).
type TcMonad = FreshMT (RWST Env () (Constraints,UniVarBindings) (ErrorT Err IO))

instance MonadFail TcMonad where
    fail = throwError . strMsg

runTcMonad :: Env -> TcMonad a -> IO (Either Err a)
runTcMonad env m = runErrorT $
                     fst <$> evalRWST (runFreshMT m) env ([], M.empty) 


-- Here are some monadic utililty functions that should really be in
-- the Haskell standard library. I guess this is a rather random place 
-- to put them, but shrug.

allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM p = liftM and . mapM p

anyM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
anyM p = liftM or . mapM p

