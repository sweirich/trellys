{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PackageImports             #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE TypeSynonymInstances       #-}
module Language.SepPP.TCUtils where

import           Language.SepPP.Options
import           Language.SepPP.PrettyPrint
import           Language.SepPP.Syntax


import           Control.Applicative        hiding (empty)
import           Control.Exception          (Exception)
import           Control.Monad.Error        hiding (join)
import           Control.Monad.Reader       hiding (join)
import           Control.Monad.State        hiding (join)
import           Data.List                  (find)
import           Data.Typeable
import           Generics.RepLib            (everywhere, mkT)
import           Text.Parsec.Pos
import           Text.PrettyPrint
import           Unbound.LocallyNameless    (Bind, Embed(..), Fresh, FreshMT, Name, aeq, bind, subst,
 translate, unbind, unrebind)


-- * The typechecking monad


newtype TCMonad a =
  TCMonad { runTCMonad :: StateT Flags (ReaderT Env (FreshMT (ErrorT TypeError IO))) a }
    deriving (Fresh, Functor, Applicative, Monad,
              MonadReader Env, MonadError TypeError, MonadState Flags, MonadIO)

-- ** The Environment
data EscapeContext = LeftContext | RightContext | StrictContext | NoContext


withEscapeContext ::  EscapeContext -> TCMonad a -> TCMonad a
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

emptyEnv :: Env
emptyEnv = Env {gamma = [], sigma = [], delta=[],rewrites=[],termProofs=[],escapeContext = NoContext}

combEnv :: Env -> Env -> Env
combEnv a b = Env { gamma = gamma a ++ gamma b
                  , sigma = sigma a ++ sigma b
                  , delta = delta a ++ delta b
                  , escapeContext = escapeContext a
                  , rewrites = rewrites a ++ rewrites b
                  , termProofs = termProofs a ++ termProofs b
                  }

instance Disp Env where
  disp env = hang (text "Context") 2 (vcat
                [disp n <> colon <+> disp t | (n,(t,_)) <- gamma env])  $$
             hang (text "Definitions") 2 (vcat
                [disp n <> colon <+> disp t | (n,t) <- sigma env])


-- | Add a new binding to an environment
extendEnv :: EName -> Expr -> Bool -> Env -> Env
extendEnv n ty isVal  e@(Env {gamma}) = e{gamma = (n,(ty,isVal)):gamma}

extendDef :: EName -> Expr -> Expr -> Bool -> Env -> Env
extendDef n ty def isVal e@(Env {sigma}) =
  extendEnv n ty isVal e { sigma = (n,def):sigma }

extendTypes :: EName -> Tele -> [(EName, (Int, Expr))] -> Env -> Env
extendTypes n tele cs e@(Env {delta}) = e{delta=(n,(tele,cs)):delta}

-- Functions for working in the environment
lookupBinding :: EName -> TCMonad (Expr,Bool)
lookupBinding n = do
  env <- asks gamma
  let fmtEnv = vcat [disp n' <> colon <+> disp ty | (n',(ty,_)) <- env]
  maybe (die $ "Can't find variable " <++> show n $$$ fmtEnv) return (lookup n env)

extendBinding :: EName -> Expr -> Bool -> TCMonad a -> TCMonad a
extendBinding n ty isVal m = do
  local (extendEnv n ty isVal) m


extendTele :: Tele -> TCMonad a -> TCMonad a
extendTele Empty m = m
extendTele (TCons binding) m = extendBinding n ty False $ extendTele rest m
  where ((n,_,Embed ty,_),rest) = unrebind binding

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
withRewrites rs m = do
  rs' <- mapM f rs
  local (\ctx -> ctx{rewrites=(rs ++ rs')}) m
  where f (l,r) = do l' <- substDefsErased l
                     return (l',r)

showRewrites :: TCMonad ()
showRewrites = do
  rs <- asks rewrites
  forM_ rs  (\(l,r) -> emit $ show l <++> "-->" <++> show r)
  tps <- asks termProofs
  forM_ tps (\t -> emit $ "TP" <++> t)


lookupRewrite :: EExpr -> TCMonad (Maybe EExpr)
lookupRewrite e = do
  e' <- noTCast <$> substDefsErased e
  rs <- asks rewrites
  -- FIXME: Is alpha-equality is too weak? Do we need actual equality?
  case find (\(l,_) -> aeq e' l || aeq e l) rs of
    Just (_,r) -> return (Just r)
    Nothing -> return Nothing


withTermProofs :: [EExpr] -> TCMonad a -> TCMonad a
withTermProofs es m = do
  es' <- mapM f es
  local (\ctx -> ctx {termProofs = (es' ++ es ++ termProofs ctx)}) m
  where f tp = substDefsErased tp

lookupTermProof :: EExpr -> TCMonad (Maybe EExpr)
lookupTermProof e = do
  e' <- noTCast <$> substDefsErased e
  tps <- asks termProofs
  return $ find (\tp -> aeq (noTCast e) tp || aeq e' tp) tps




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
          messages = [ei | ei@(ErrInfo _ _) <- info]
          details = concat [ds | ErrInfo _ ds <- info]

          pos ((ErrLoc sp _):_) = disp sp
          pos _ = text "unknown" <> colon
          summary = vcat [s | ErrInfo s _ <- messages]
          detailed = vcat [(int i <> colon <+> brackets label) <+> d |
                           (label,d) <- details | i <- [1..]]
          terms = [hang (text "In the term") 2 (disp t) | ErrLoc _ t <- take 4 positions]


addErrorPos ::  SourcePos -> Expr -> TypeError -> TCMonad a
addErrorPos p t (ErrMsg ps) = throwError (ErrMsg (ErrLoc p t:ps))

-- err msg = throwError (strMsg msg)

ensure :: Disp d => Bool -> d -> TCMonad ()
ensure p m = do
  unless p $ die m

die :: Disp d => d -> TCMonad a
die msg = do
  typeError (disp msg) []


typeError :: Disp d => d -> [(Doc, Doc)] -> TCMonad a
typeError summary details = throwError (ErrMsg [ErrInfo (disp summary) details])

addErrorInfo :: Disp d => d -> [(Doc, Doc)] -> TypeError -> TypeError
addErrorInfo summary details (ErrMsg ms) = ErrMsg (ErrInfo (disp summary) details:ms)

withErrorInfo :: (Disp d) => d -> [(Doc, Doc)] -> TCMonad a -> TCMonad a
withErrorInfo summary details m = m `catchError` (throwError . addErrorInfo summary details)


emit :: (Show a, MonadIO m) => a -> m ()
emit m = liftIO $ print m

sameType :: Expr -> Maybe Expr -> TCMonad ()
_ `sameType` Nothing = return ()
actual `sameType` (Just expected) = actual `expectType` expected


expectType :: Expr -> Expr -> TCMonad ()
actual `expectType` expected = do
  printAST <- getOptPrintAST
  -- We erase tcasts when comparing types
  unless (down (eraseTCast actual) `aeq` down (eraseTCast expected)) $
    typeError "Couldn't match expected type with actual type."
                ([(text "Expected Type",disp expected)
               , (text "Actual Type", disp actual)] ++ ast printAST)
 where ast True =  [(text "Expected AST", text $ show $ downAll  expected)
                   , (text "Actual AST", text $ show $ downAll actual)
                   ]
       ast False = []
       eraseTCast = everywhere (mkT unTCast)
         where unTCast (TCast t _) = t
               unTCast t = t


(<++>) :: (Show t1, Show t2, Disp t1, Disp t2) => t1 -> t2 -> Doc
t1 <++> t2 = disp t1 <+> disp t2

($$$) :: (Disp d, Disp d1) => d -> d1 -> Doc
t1 $$$ t2 =  disp t1 $$ disp t2



-------------------------------------
-- syntactic Value

synValue :: Expr -> TCMonad Bool
synValue (Var x) =
  do (_,valuep) <- lookupBinding x
     return valuep
synValue (Con _) = return True
synValue (Formula _) = return True
synValue Type = return True
synValue (Pi _ _) = return True
synValue (Lambda _ _ _) = return True
synValue (Pos _ t) = synValue t
synValue (Ann t _) = synValue t
synValue (Rec _) = return True
synValue (TCast _ _) = return True
synValue (ConvCtx t _) = synValue t
synValue (App f stage x) = liftM2 (&&) (constrApp f) (argValue stage)
  where constrApp (Con _) = return True
        constrApp (App f' Static _) = constrApp f'
        constrApp (App f' Dynamic x') = liftM2 (&&) (constrApp f') (synValue x')
        constrApp (Pos _ t) = constrApp t
        constrApp _ = return False
        argValue Dynamic = synValue x
        argValue _ = return True
synValue _ = return False


-- This is the isValue judgement on erased terms. It allows us to judge
-- variables marked as 'values' in the type environment to be values.
erasedSynValue :: EExpr -> TCMonad Bool
erasedSynValue (EVar x) = do
  do (_,valuep) <- lookupBinding (translate x)
     return valuep
erasedSynValue (ETCast _) = return True
erasedSynValue (ECon _) = return True
erasedSynValue EType = return True
erasedSynValue (ELambda _) = return True
erasedSynValue (ERec _) = return True
erasedSynValue (EApp f x) = liftM2 (&&) (constrApp f) (erasedSynValue x)
  where constrApp (ECon _) = return True
        constrApp (EApp f' x') = liftM2 (&&) (constrApp f') (erasedSynValue x')
        constrApp _ = return False
erasedSynValue _ = return False



-- | Erase an annotated term into an unannotated term, for evaluation.
-- Erasure is complicated slightly because we need to know the stage
-- (static or dynamic) of pattern variables, which is available in the
-- *types* of the data constructors.
erase :: (Applicative m, Fresh m) => Expr -> m EExpr
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
  ((n,Embed tp,_),body) <- unbind binding
  et <- erase tp
  EPi s <$> ((bind ((translate n),Embed et)) <$> erase body)
erase (Rec binding) = do
  ((n,tele),body) <- unbind binding
  ns <- eraseTele tele
  ERec <$> (bind (translate n, ns)) <$> erase body
    where eraseTele :: Monad m => Tele -> m [EEName]
          eraseTele Empty = return []
          eraseTele (TCons rebinding) = do
            let ((n,stage,Embed _ty,_inf),rest) = unrebind rebinding
            ns <- eraseTele rest
            case stage of
              Dynamic -> return (translate n:ns)
              Static -> return ns

erase (Case scrutinee _ binding) = do
  (_,alts) <- unbind binding
  ECase <$> erase scrutinee <*> mapM eraseAlt alts

erase (Let stage binding) = do
  ((x,_,Embed t),body) <- unbind binding
  if (isProof t || stage == Static)
    then erase body
    else do
      et <- erase t
      ebody <- erase body
      return $ ELet (bind (translate x,Embed et) ebody)

  where isProof (Pos _ e)  = isProof e
        isProof (Ann e _) = isProof e
        isProof (Tactic (MoreJoin _)) = True
        isProof (Join _ _) = True
        isProof (Tactic (Sym _)) = True
        isProof (Tactic (Trans _ _)) = True
        isProof (ConvCtx s _) = isProof s
        isProof (TerminationCase _ _) = True -- Wrong. This disallows terminationcase in a program.
        -- FIXME: This should check the syntactic class of the  definiens, not this hacky definition.
        isProof _ = False
erase (EElim _ binding) = do
  ((_,_),body) <- unbind binding
  erase body

erase (ConvCtx v _) = erase v
erase (Ann t _) = erase t
erase (Abort _) = return EAbort
erase (Show t) = erase t
erase (TCast t _) = ETCast <$> erase t
erase (Tactic (Autoconv t)) = erase t

erase t =  do
  fail $  "The erasure function is not defined on: " ++ show (downAll t)

eraseAlt :: (Applicative m, Fresh m) =>
             Bind (String, [(EName,Stage)]) Expr ->  m (Bind (String, [EEName]) EExpr)
eraseAlt binding = do
  ((c,vs),body) <- unbind binding
  -- erasePatVars looks at _all_ data constructors, which isn't
  -- particularly efficient. To restrict this to just constructors of
  -- the type of the scrutinee would require erasure to be
  -- type-directed, which is a can of worms that we don't need to open
  -- for the time being.
  let vs' = [translate v | (v,Dynamic) <- vs]
  -- vs' <- erasePatVars c vs
  bind (c,vs') <$> erase body
