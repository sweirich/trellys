module Language.SepCore.Rewriting where

import Language.SepCore.Syntax
import Language.SepCore.PrettyPrint

import Generics.RepLib hiding (Con(..))
import Unbound.LocallyNameless hiding (Con(..),Equal,Refl)
import "mtl" Control.Monad.Trans
import Control.Applicative
import Control.Monad
import "mtl" Control.Monad.Error
import Text.PrettyPrint(render, text,(<+>),($$))



