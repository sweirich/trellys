{-# LANGUAGE NamedFieldPuns, FlexibleInstances, TypeSynonymInstances, DeriveDataTypeable, GeneralizedNewtypeDeriving, ParallelListComp #-}
module Language.SepPP.TCUtils where

import Language.SepPP.Syntax
import Language.SepPP.PrettyPrint


import Unbound.LocallyNameless(Name, Fresh,FreshMT,runFreshMT,aeq,substs,subst)

import Text.PrettyPrint
import Data.Typeable
import Control.Monad.Reader hiding (join)
import Control.Monad.Error hiding (join)
import Control.Exception(Exception)
import Control.Applicative hiding (empty)
import Text.Parsec.Pos
import Data.List(find)

-- * The typechecking monad

newtype TCMonad a =
  TCMonad { runTCMonad :: ReaderT Env (FreshMT (ErrorT TypeError IO)) a }
    deriving (Fresh, Functor, Applicative, Monad,
              MonadReader Env, MonadError TypeError, MonadIO)



-- ** The Environment
data EscapeContext = LeftContext | RightContext | StrictContext | NoContext
withEscapeContext c = local (\env -> env { escapeContext = c })

-- The typing context contains a mapping from variable names to types, with
-- an additional boolean indicating if it the variable is a value.
data Env = Env { gamma :: [(TName,(Term,Bool))]   -- (var, (type,isValue))
               , sigma :: [(TName,Term)]          -- (var, definition)
               , delta :: [(TName,[(TName,Int)])] -- (type constructor, [(data cons, arity)])
               , escapeContext :: EscapeContext
               , rewrites :: [(ETerm,ETerm)]}
emptyEnv = Env {gamma = [], sigma = [], delta=[],rewrites=[],escapeContext = NoContext}



-- | Add a new binding to an environment
extendEnv n ty isVal  e@(Env {gamma}) = e{gamma = (n,(ty,isVal)):gamma}
extendDef n ty def isVal e@(Env {sigma}) =
  extendEnv n ty isVal e { sigma = (n,def):sigma }
extendTypes n cs e@(Env {delta}) = e{delta=(n,cs):delta}

-- Functions for working in the environment
lookupBinding :: TName -> TCMonad (Term,Bool)
lookupBinding n = do
  env <- asks gamma
  let fmtEnv = vcat [disp n <> colon <+> disp ty | (n,(ty,_)) <- env]
  maybe (die $ "Can't find variable " <++> show n $$$ fmtEnv) return (lookup n env)

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


lookupDef :: Name Term -> TCMonad (Maybe Term)
lookupDef n = do
  defs <- asks sigma
  return $ lookup n defs


substDefs :: Term -> TCMonad Term
substDefs t = do
  defs <- asks sigma
  -- mapM (\t-> doDisp (fst t) >>= (liftIO . print)) defs
  return $ substs defs t

withRewrites :: [(ETerm,ETerm)] -> TCMonad a -> TCMonad a
withRewrites rs m = local (\ctx -> ctx{rewrites=rs}) m

lookupRewrite :: ETerm -> TCMonad (Maybe ETerm)
lookupRewrite e = do
  rs <- asks rewrites
  -- FIXME: alpha-equality is too week. We need actual equality.
  case find (\(l,r) -> aeq e l) rs of
    Just (_,r) -> return (Just r)
    Nothing -> return Nothing


-- ** Error handling

data TypeError = ErrMsg [ErrInfo] deriving (Show,Typeable)

data ErrInfo = ErrInfo Doc -- A Summary
                       [(Doc,Doc)] -- A list of details
             | ErrLoc SourcePos Term deriving (Show,Typeable)

instance Error TypeError where
  strMsg s = ErrMsg [ErrInfo (text s) []]
  noMsg = strMsg "<unknown>"


instance Exception TypeError

instance Disp TypeError where

  disp (ErrMsg rinfo) =
       hang (pos positions) 2 (summary $$ nest 2 detailed $$  vcat terms)
    where info = reverse rinfo
          positions = [el | el@(ErrLoc _ _) <- info]
          messages = [ei | ei@(ErrInfo d _) <- info]
          details = concat [ds | ErrInfo _ ds <- info]

          pos ((ErrLoc sp _):_) = disp sp
          pos _ = text "unknown" <> colon
          summary = vcat [s | ErrInfo s _ <- messages]
          detailed = vcat [(int i <> colon <+> brackets label) <+> d |
                           (label,d) <- details | i <- [1..]]
          terms = [hang (text "In the term") 2 (disp t) | ErrLoc _ t <- take 2 positions]


addErrorPos p t (ErrMsg ps) = throwError (ErrMsg (ErrLoc p t:ps))

err msg = throwError (strMsg msg)

ensure p m = do
  unless p $ die m

die msg = do
  typeError (disp msg) []


typeError summary details = throwError (ErrMsg [ErrInfo (disp summary) details])

addErrorInfo summary details (ErrMsg ms) = ErrMsg (ErrInfo (disp summary) details:ms)
withErrorInfo summary details m = m `catchError` (throwError . addErrorInfo summary details)

emit m = liftIO $ print m

actual `sameType` Nothing = return ()
actual `sameType` (Just expected) = actual `expectType` expected

actual `expectType` expected =
  unless (actual `aeq` expected) $
    typeError "Couldn't match expected type with actual type."
                [(text "Expected Type",disp expected),
                 (text "Actual Type", disp actual)]


(<++>) :: (Show t1, Show t2, Disp t1, Disp t2) => t1 -> t2 -> Doc
t1 <++> t2 = disp t1 <+> disp t2
t1 $$$ t2 =  disp t1 $$ disp t2



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
synValue (Ann t typ) = synValue t
synValue (Rec _) = return True
synValue (App f _ x) = lift2 (&&) (constrApp f) (synValue x)
  where constrApp (Con c) = return True
        constrApp (App f _ x) = lift2 (&&) (constrApp f) (synValue x)
        constrApp (Pos x t) = constrApp t
        constrApp _ = return False

synValue x = return False
