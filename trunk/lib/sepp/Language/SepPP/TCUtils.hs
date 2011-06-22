{-# LANGUAGE NamedFieldPuns, FlexibleInstances, TypeSynonymInstances, DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
module Language.SepPP.TCUtils where

import Language.SepPP.Syntax
import Language.SepPP.PrettyPrint


import Unbound.LocallyNameless(Fresh,FreshMT,runFreshMT,aeq,substs)

import Text.PrettyPrint
import Data.Typeable
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)
import Control.Exception(Exception)
import Control.Applicative
import Text.Parsec.Pos


-- * The typechecking monad

newtype TCMonad a =
  TCMonad { runTCMonad :: ReaderT Env (FreshMT (ErrorT TypeError IO)) a }
  deriving (Fresh, Functor, Monad, MonadReader Env, MonadError TypeError, MonadIO)



-- ** The Environment
data EscapeContext = LeftContext | RightContext | StrictContext | NoContext
withEscapeContext c = local (\env -> env { escapeContext = c })

-- The typing context contains a mapping from variable names to types, with
-- an additional boolean indicating if it the variable is a value.
data Env = Env { gamma :: [(TName,(Term,Bool))]   -- (var, (type,isValue))
               , sigma :: [(TName,Term)]          -- (var, definition)
               , delta :: [(TName,[(TName,Int)])] -- (type constructor, [(data cons, arity)])
               , escapeContext :: EscapeContext }
emptyEnv = Env {gamma = [], sigma = [], delta=[],escapeContext = NoContext}



-- | Add a new binding to an environment
extendEnv n ty isVal  e@(Env {gamma}) = e{gamma = (n,(ty,isVal)):gamma}
extendDef n ty def isVal e@(Env {sigma}) =
  extendEnv n ty isVal e { sigma = (n,def):sigma }
extendTypes n cs e@(Env {delta}) = e{delta=(n,cs):delta}

-- Functions for working in the environment
lookupBinding :: TName -> TCMonad (Term,Bool)
lookupBinding n = do
  env <- asks gamma
  maybe (err $ "Can't find variable " ++ show n ++ "\n" ++ show env) return (lookup n env)
extendBinding :: TName -> Term -> Bool -> TCMonad a -> TCMonad a
extendBinding n ty isVal m = do
  local (extendEnv n ty isVal) m

extendDefinition :: TName -> Term -> Term -> Bool -> TCMonad a -> TCMonad a
extendDefinition n ty def isVal m = do
  local (extendDef n ty def isVal) m


extendTypeCons :: TName -> [(TName,Int)] -> TCMonad a -> TCMonad a
extendTypeCons n cs m = do
  local (extendTypes n cs) m


lookupTypeCons :: TName -> TCMonad [(TName,Int)]
lookupTypeCons nm = do
  d <- asks delta
  case lookup nm d of
    Nothing -> die $ "Can't find type constructor " <++> nm <++> show d

    Just cs -> return cs




substDefs :: Term -> TCMonad Term
substDefs t = do
  defs <- asks sigma
  return $ substs defs t



-- ** Error handling

data TypeError = ErrMsg [(SourcePos,Term)] String deriving (Show,Typeable)

instance Error TypeError where
  strMsg s = ErrMsg [] s
  noMsg = strMsg "<unknown>"


instance Exception TypeError

instance Disp TypeError where
  disp (ErrMsg [] msg) = return
          (nest 2 (text "Type Error" $$
              text msg))

  disp (ErrMsg ps msg) = return
     (start $$
      nest 2 (text "Type Error" $$
              text msg))
    where (p,t) = last ps
          start = text (show p)



addErrorPos p t (ErrMsg ps msg) = throwError (ErrMsg ((p,t):ps) msg)

err msg = throwError (strMsg msg)

ensure p m = do
  unless p $ m >>= (err . render)

die m = do
  m >>= (err . render)

actual `expectType` expected =
  ensure (actual `aeq` expected)
           ("Expecting '" <++> expected <++> "' but actual type is " <++> actual)


t1 <++> t2 = liftM2 (<+>) (doDisp t1) (doDisp t2)
t1 $$$ t2 = liftM2 ($$) (doDisp t1) (doDisp t2)

class IsDisp a where
  doDisp :: a -> TCMonad Doc

instance IsDisp String where
  doDisp s = return $ text s
instance IsDisp Int where
  doDisp i = return $ int i
-- instance Disp a => IsDisp a where
--   doDisp = disp
instance IsDisp TName where
  doDisp n = disp n
instance IsDisp Term where
  doDisp t = disp t
instance  IsDisp (TCMonad Doc) where
  doDisp m = m



-------------------------------------
-- syntactic Value

lift2 f c1 c2 = do { x<-c1; y<-c2; return(f x y)}
lift1 f c1 = do { x<-c1; return(f x)}


synValue (Var x) =
  do (term,valuep) <- lookupBinding x
     return valuep
synValue (Con c) = return True
synValue (Formula n) = return True
synValue Type = return True
synValue (Pi stg bdngs) = return True
synValue (Lambda k stg bndgs) = return True
synValue (Pos n t) = synValue t
synValue (Parens t) = synValue t
synValue (Ann t typ) = synValue t
synValue (App f _ x) = lift2 (&&) (constrApp f) (synValue x)
  where constrApp (Con c) = return True
        constrApp (App f _ x) = lift2 (&&) (constrApp f) (synValue x)
        constrApp (Parens t) = constrApp t
        constrApp (Pos x t) = constrApp t
        constrApp _ = return False

synValue x = return False
