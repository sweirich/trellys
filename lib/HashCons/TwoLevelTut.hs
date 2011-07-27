{-# LANGUAGE MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
  #-}

import Unbound.LocallyNameless

import Control.Applicative
import Control.Arrow ((+++))
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Error

import Text.Parsec hiding ((<|>), Empty)
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)

import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>))


{- -- making this into 2-level types
data Term = Var (Name Term)
          | App Term Term
          | Lam (Bind (Name Term) Term)
  deriving Show
-}

data TermF nm t
  = Var nm
  | App t t
  | Lam (Bind nm t)
  deriving Show

data Term = T (TermF (Name Term) Term)
  deriving Show

$(derive [''Term,''TermF])

instance (Alpha a, Alpha b) => Alpha (TermF (Name a) b)
instance Alpha Term

instance (Alpha a, Alpha b, Subst t b) => Subst t (TermF (Name a) b) where
--  isvar (Var v) = error "what do I have to write here???"
--  isvar _       = Nothing

instance Subst Term Term where
  isvar (T (Var v)) = Just (SubstName v)
  isvar _           = Nothing

lam :: String -> Term -> Term
lam x t = T $ Lam $ bind (string2Name x) t

var :: String -> Term
var = T . Var . string2Name

app :: Term -> Term -> Term
app x y = T (App x y)

-- A convenient synonym for mzero
done :: MonadPlus m => m a
done = mzero

step :: Term -> MaybeT FreshM Term
step (T(Var _)) = done
step (T(Lam _)) = done
step (T(App (T(Lam b)) t2)) = do
  (x,t1) <- unbind b
  return $ subst x t2 t1
step (T(App t1 t2)) =
      app <$> step t1 <*> pure t2
  <|> app <$> pure t1 <*> step t2

tc :: (Monad m, Functor m) => (a -> MaybeT m a) -> (a -> m a)
tc f a = do
  ma' <- runMaybeT (f a)
  case ma' of
    Just a' -> tc f a'
    Nothing -> return a

eval :: Term -> Term
eval x = runFreshM (tc step x)

lexer    = P.makeTokenParser haskellDef
parens   = P.parens lexer
brackets = P.brackets lexer
ident    = P.identifier lexer

parseTerm = parseAtom `chainl1` (pure app)

parseAtom = parens parseTerm
        <|> var <$> ident
        <|> lam <$> (brackets ident) <*> parseTerm

runTerm :: String -> Either ParseError Term
runTerm = (id +++ eval) . parse parseTerm ""

class Pretty' p where
  ppr' :: (Applicative m, Fresh m) => p -> m Doc

instance Pretty' Term where
  ppr' (T(Var x))     = return . PP.text . show $ x
  ppr' (T(App t1 t2)) = PP.parens <$> ((<+>) <$> ppr' t1 <*> ppr' t2)
  ppr' (T(Lam b))     = do
    (x, t) <- unbind b
    ((PP.brackets . PP.text . show $ x) <+>) <$> ppr' t

class Pretty p where
  ppr :: (Applicative m, LFresh m) => p -> m Doc

instance Pretty Term where
  ppr (T(Var x))     = return . PP.text . show $ x
  ppr (T(App t1 t2)) = PP.parens <$> ((<+>) <$> ppr t1 <*> ppr t2)
  ppr (T(Lam b))     =
    lunbind b $ \(x,t) ->
      ((PP.brackets . PP.text . show $ x) <+>) <$> ppr t

