{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports,ParallelListComp #-}





import Unbound.LocallyNameless hiding (name,Infix,Val,Con)
import Text.Parsec hiding (ParseError,Empty)
import Text.Parsec.Error(errorMessages, messageString)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token

import Data.Typeable
import Control.Applicative hiding ((<|>),many)
import "mtl" Control.Monad.Identity
import Control.Exception(Exception)
import Data.Char
import Text.PrettyPrint(render)

-- | Parse a string to module.
parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts = runParser sepModule () srcName cnts
