{-# LANGUAGE TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , OverlappingInstances
           , MultiParamTypeClasses
           , UndecidableInstances
  #-}

module Language.Trellys.FreshT where

-- The following is copy-pasted from the definition of FreshMT in Unbound,
-- with the difference that I don't derive MonadState Integer, since 
-- that interfers with the other state I want to track...


import Language.Trellys.GenericBind(Fresh(..), Name(..))


import Data.Set (Set)
import qualified Data.Set as S

import Data.Monoid

import Control.Monad.Reader
import qualified Control.Monad.State as St
import Control.Monad.Identity
import Control.Applicative (Applicative)

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Error
import Control.Monad.Trans.Identity
import Control.Monad.Trans.List
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.State.Lazy as Lazy
import Control.Monad.Trans.State.Strict as Strict
import Control.Monad.Trans.Writer.Lazy as Lazy
import Control.Monad.Trans.Writer.Strict as Strict

import qualified Control.Monad.Cont.Class as CC
import qualified Control.Monad.Error.Class as EC
import qualified Control.Monad.State.Class as StC
import qualified Control.Monad.Reader.Class as RC
import qualified Control.Monad.IO.Class as IC

newtype FreshMT' m a = FreshMT' { unFreshMT' :: St.StateT Integer m a }
  deriving (Functor, Applicative, Monad, MonadPlus, MonadIO, MonadFix)

runFreshMT' :: Monad m => FreshMT' m a -> m a
runFreshMT' m = contFreshMT' m 0

contFreshMT' :: Monad m => FreshMT' m a -> Integer -> m a
contFreshMT' (FreshMT' m) = St.evalStateT m

instance Monad m => Fresh (FreshMT' m) where
  fresh (Nm r (s,_)) = FreshMT' $ do
    n <- St.get
    St.put (n+1)
    return $ Nm r (s,n)

-- Instances for applying FreshMT' to other monads

instance MonadTrans FreshMT' where
  lift = FreshMT' . lift

instance CC.MonadCont m => CC.MonadCont (FreshMT' m) where
  callCC c = FreshMT' $ CC.callCC (unFreshMT' . (\k -> c (FreshMT' . k)))

instance EC.MonadError e m => EC.MonadError e (FreshMT' m) where
  throwError = lift . EC.throwError
  catchError m h = FreshMT' $ EC.catchError (unFreshMT' m) (unFreshMT' . h)

instance StC.MonadState s m => StC.MonadState s (FreshMT' m) where
  get = lift StC.get
  put = lift . StC.put

instance RC.MonadReader r m => RC.MonadReader r (FreshMT' m) where
  ask   = lift RC.ask
  local f = FreshMT' . RC.local f . unFreshMT'

