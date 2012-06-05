
{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, GeneralizedNewtypeDeriving,
NamedFieldPuns, TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
PackageImports,ParallelListComp, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

module Language.SepCore.Error where
import Language.SepCore.Syntax
import Language.SepCore.Lexer
import Language.SepCore.Parser
import Language.SepCore.PrettyPrint
import Unbound.LocallyNameless( Embed(..),Name, Fresh,FreshMT,runFreshMT,aeq,substs,subst,embed, unrebind,translate, bind, unbind, string2Name)
import Control.Monad.Error hiding (join)


import Text.PrettyPrint
import Data.Typeable
import Control.Exception(Exception)
import Control.Applicative hiding (empty)


data TypeError = ErrMsg [ErrInfo] 
               deriving (Show,Typeable)

data ErrInfo = ErrInfo Doc
             | ErrLoc AlexPosn Expr
             deriving (Show,Typeable)

instance Error TypeError where
  strMsg s = ErrMsg [ErrInfo (text s)]
  noMsg = strMsg "<unknown>"

instance Exception TypeError

instance Disp TypeError where
  disp (ErrMsg rinfo) =
       hang (pos positions) 2 (summary $$ vcat terms)
    where info = reverse rinfo
          positions = [el | el@(ErrLoc _ _) <- info]
          messages = [ei | ei@(ErrInfo d) <- info]
          pos ((ErrLoc sp _):_) = disp sp
          pos _ = text "unknown position" <> colon
          summary = vcat [s | ErrInfo s <- messages]
          terms = [hang (text "In the expression") 2 (disp t) | ErrLoc _ t <- take 4 positions]

addErrorPos p t (ErrMsg ps) = throwError (ErrMsg (ErrLoc p t:ps))

err msg = throwError (strMsg msg)

typeError summary = throwError (ErrMsg [ErrInfo  summary])

addErrorInfo summary (ErrMsg ms) = ErrMsg (ErrInfo (disp summary):ms)


