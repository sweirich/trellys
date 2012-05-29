module Language.SepCore.Error where
-- This file is based on Garrin's TCUtils.hs file. 
import Language.SepCore.Syntax
import Language.SepCore.Lexer(Alex)
import Language.SepCore.Parser

import Language.SepCore.PrettyPrint
import Unbound.LocallyNameless( Embed(..),Name, Fresh,FreshMT,runFreshMT,aeq,substs,subst,embed, unrebind,translate, bind, unbind, string2Name)

import Text.PrettyPrint
import Data.Typeable
import "mtl" Control.Monad.Reader hiding (join)
import "mtl" Control.Monad.Error hiding (join)
import "mtl" Control.Monad.State hiding (join)
import Control.Exception(Exception)
import Control.Applicative hiding (empty)


data TypeError = ErrMsg [ErrInfo] deriving (Show,Typeable)
data ErrInfo = ErrInfo Doc -- A Summary
                       [(Doc,Doc)] -- A list of details
             | ErrLoc SourcePos Expr deriving (Show,Typeable)

