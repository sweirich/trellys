{-# LANGUAGE NamedFieldPuns, FlexibleInstances, TypeSynonymInstances, DeriveDataTypeable, GeneralizedNewtypeDeriving, ParallelListComp, PackageImports #-}
module Language.SepPP.TCUtils where

import Language.SepPP.Syntax
import Language.SepPP.PrettyPrint
import Language.SepPP.Options


import Unbound.LocallyNameless( Embed(..),Name, Fresh,FreshMT,runFreshMT,aeq,substs,subst,embed, unrebind,translate, bind, unbind, string2Name)

import Text.PrettyPrint
import Data.Typeable
import "mtl" Control.Monad.Reader hiding (join)
import "mtl" Control.Monad.Error hiding (join)
import "mtl" Control.Monad.State hiding (join)
import Control.Exception(Exception)
import Control.Applicative hiding (empty)
import Text.Parsec.Pos
import Data.List(find)
import qualified Data.Map as M

-- * The typechecking monad


newtype TCMonad a =
  TCMonad { runTCMonad :: StateT Flags (ReaderT Env (FreshMT (ErrorT TypeError IO))) a }
    deriving (Fresh, Functor, Applicative, Monad,
              MonadReader Env, MonadError TypeError, MonadState Flags, MonadIO)

-- ** The Environment
data EscapeContext = LeftContext | RightContext | StrictContext | NoContext
withEscapeContext c = local (\env -> env { escapeContext = c })

-- The typing context contains a mapping from variable names to types, with
-- an additional boolean indicating if it the variable is a value.
data Env = Env { gamma :: [(EName,(Expr,Bool))]   -- (var, (type,isValue))
               , sigma :: [(EName,Expr)]          -- (var, definition)
               , delta :: [(EName,(Tele,[(EName,(Int,Expr))]))]
                   -- (type constructor, [(data cons, arity, type)])
               , escapeContext :: EscapeContext
               -- rewrites and termproofs are used by morejoin to drive reduction.
               , rewrites :: [(EExpr,EExpr)]
               , termProofs :: [EExpr]}
emptyEnv = Env {gamma = [], sigma = [], delta=[],rewrites=[],termProofs=[],escapeContext = NoContext}


instance Disp Env where
  disp env = hang (text "Context") 2 (vcat
                [disp n <> colon <+> disp t | (n,(t,_)) <- gamma env])  $$
             hang (text "Definitions") 2 (vcat
                [disp n <> colon <+> disp t | (n,t) <- sigma env])


-- | Add a new binding to an environment
extendEnv n ty isVal  e@(Env {gamma}) = e{gamma = (n,(ty,isVal)):gamma}
extendDef n ty def isVal e@(Env {sigma}) =
  extendEnv n ty isVal e { sigma = (n,def):sigma }
extendTypes n tele cs e@(Env {delta}) = e{delta=(n,(tele,cs)):delta}

-- Functions for working in the environment
lookupBinding :: EName -> TCMonad (Expr,Bool)
lookupBinding n = do
  env <- asks gamma
  let fmtEnv = vcat [disp n <> colon <+> disp ty | (n,(ty,_)) <- env]
  maybe (die $ "Can't find variable " <++> show n) return (lookup n env)

extendBinding :: EName -> Expr -> Bool -> TCMonad a -> TCMonad a
extendBinding n ty isVal m = do
  local (extendEnv n ty isVal) m


extendTele :: Tele -> TCMonad a -> TCMonad a
extendTele Empty m = m
extendTele (TCons binding) m = extendBinding n ty False $ extendTele rest m
  where ((n,st,Embed ty),rest) = unrebind binding

extendDefinition :: EName -> Expr -> Expr -> Bool -> TCMonad a -> TCMonad a
extendDefinition n ty def isVal m = do
  local (extendDef n ty def isVal) m


extendTypeCons :: EName -> Tele -> [(EName,(Int,Expr))] -> TCMonad a -> TCMonad a
extendTypeCons n tele cs m = do
  local (extendTypes n tele cs) m


lookupTypeCons :: EName -> TCMonad (Tele,[(EName,(Int,Expr))])
lookupTypeCons nm = do
  d <- asks delta
  case lookup nm d of
    Nothing -> die $ "Can't find type constructor " <++> nm <++> show d

    Just cs -> return cs


lookupDef :: Name Expr -> TCMonad (Maybe Expr)
lookupDef n = do
  defs <- asks sigma
  return $ lookup n defs


substDefs :: Expr -> TCMonad Expr
substDefs t = do
  defs <- asks sigma
  return $ foldl (\tm (nm,def) -> subst nm def tm) t defs
  -- return $ substs defs t


substDefsErased :: EExpr -> TCMonad EExpr
substDefsErased e = do
  defs <- asks sigma
  edefs <- sequence [(,) (translate n) <$> erase t | (n,t) <- defs]
  return $ foldl (\tm (nm,def) -> subst nm def tm) e edefs


withRewrites :: [(EExpr,EExpr)] -> TCMonad a -> TCMonad a
withRewrites rs m = local (\ctx -> ctx{rewrites=rs}) m

lookupRewrite :: EExpr -> TCMonad (Maybe EExpr)
lookupRewrite e = do
  rs <- asks rewrites
  -- FIXME: Is alpha-equality is too weak? Do we need actual equality?
  case find (\(l,r) -> aeq e l) rs of
    Just (_,r) -> return (Just r)
    Nothing -> return Nothing


withTermProofs :: [EExpr] -> TCMonad a -> TCMonad a
withTermProofs es m = do
  local (\ctx -> ctx {termProofs = es ++ termProofs ctx}) m

lookupTermProof :: EExpr -> TCMonad (Maybe EExpr)
lookupTermProof e = do
  tps <- asks termProofs
  return $ find (aeq e) tps




-- ** Error handling

data TypeError = ErrMsg [ErrInfo] deriving (Show,Typeable)

data ErrInfo = ErrInfo Doc -- A Summary
                       [(Doc,Doc)] -- A list of details
             | ErrLoc SourcePos Expr deriving (Show,Typeable)

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
          terms = [hang (text "In the term") 2 (disp t) | ErrLoc _ t <- take 4 positions]


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
  unless (down actual `aeq` down expected) $
    typeError "Couldn't match expected type with actual type."
                [(text "Expected Type",disp expected)
                , (text "Actual Type", disp actual)
--                , (text "Expected AST", text $ show $ downAll  expected)
--                , (text "Actual AST", text $ show $ downAll actual)
                ]


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
        constrApp (App f Static x) = constrApp f
        constrApp (App f Dynamic x) = lift2 (&&) (constrApp f) (synValue x)
        constrApp (Pos x t) = constrApp t
        constrApp _ = return False
synValue x = return False


-- This is the isValue judgement on erased terms. It allows us to judge
-- variables marked as 'values' in the type environment to be values.
erasedSynValue (EVar x) = do
  do (term,valuep) <- lookupBinding (translate x)
     return valuep
erasedSynValue (ECon c) = return True
erasedSynValue EType = return True
-- erasedSynValue (Pi stg bdngs) = return True
erasedSynValue (ELambda bndgs) = return True
-- erasedSynValue (Pos n t) = synValue t
-- erasedSynValue (Ann t typ) = synValue t
erasedSynValue (ERec _) = return True
erasedSynValue (EApp f x) = lift2 (&&) (constrApp f) (erasedSynValue x)
  where constrApp (ECon c) = return True
        constrApp (EApp f x) = lift2 (&&) (constrApp f) (erasedSynValue x)
        constrApp _ = return False
erasedSynValue x = return False



-- Erasure
-- | Erase an annotated term into an unannotated term, for evaluation.
--- erase :: (Applicative m, Fresh m ) => Expr -> m EExpr
erase (Pos _ t) = erase t
erase Type = return EType
erase (Var n) = return $ EVar (translate n)
erase (Con n) = return $ ECon (translate n)
erase (App f Static _) = erase f
erase (App f Dynamic x) = EApp <$> (erase f) <*> (erase x)
erase (Lambda _ Static binding) = do
  (_,body) <- unbind binding
  erase body
erase (Lambda _ Dynamic binding) = do
  ((n,_),body) <- unbind binding
  ELambda <$> ((bind (translate n)) <$> erase body)
erase (Pi s binding) = do
  ((n,Embed tp),body) <- unbind binding
  et <- erase tp
  EPi s <$> ((bind ((translate n),Embed et)) <$> erase body)
erase (Rec binding) = do
  ((n,tele),body) <- unbind binding
  ns <- eraseTele tele
  ERec <$> (bind (translate n, ns)) <$> erase body
  where eraseTele :: Monad m => Tele -> m [EEName]
        eraseTele Empty = return []
        eraseTele (TCons rebinding) = do
          let ((n,stage,Embed ty),rest) = unrebind rebinding
          ns <- eraseTele rest
          case stage of
            Dynamic -> return (translate n:ns)
            Static -> return ns

erase (Case scrutinee _ binding) = do
    (_,alts) <- unbind binding
    ECase <$> erase scrutinee <*> mapM eraseAlt alts
  where eraseAlt binding = do
          ((c,vs),body) <- unbind binding
          -- erasePatVars looks at _all_ data constructors, which isn't
          -- particularly efficient. To restrict this to just constructors of
          -- the type of the scrutinee would require erasure to be
          -- type-directed, which is a can of worms that we don't need to open
          -- for the time being.
          vs' <- erasePatVars c vs
          bind (c,map translate vs') <$> erase body

erase (Let binding) = do
    ((x,_,Embed t),body) <- unbind binding
    et <- erase t
    ebody <- erase body
    return $ ELet (bind (translate x,Embed et) ebody)

erase (ConvCtx v _) = erase v
erase (Ann t _) = erase t

erase t =  do
  fail $  "The erasure function is not defined on: " ++ show (downAll t)


-- Drop pattern variables that correspond to erased /constructor/
-- parameters. The lookup should be memoized.
erasePatVars :: String -> [EName] -> TCMonad [EName]
erasePatVars cname vars = do
  tcs <- asks delta
  let constructors = [(n,ty) | (tc,(_,cons)) <- tcs, (n,(arity,ty)) <- cons]
  case lookup (string2Name cname) constructors of
    Nothing -> typeError "Could not find constructor."
                   [(text "The constructor",disp cname)]
    Just ty -> piArgs ty vars

  where piArgs (Pos _ t) vs = piArgs t vs
        piArgs (Pi st binding) (v:vs) = do
          (_,body) <- unbind binding
          vs' <- piArgs body vs
          case st of
            Static -> return $ vs'
            Dynamic -> return $ v:vs'
        piArgs _ _ = return []


