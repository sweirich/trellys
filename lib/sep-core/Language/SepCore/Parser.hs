{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports,ParallelListComp #-}

module Language.SepCore.Parser where
import Language.SepCore.Syntax
import Text.ParserCombinators.Parsec hiding (spaces)
-- import Unbound.LocallyNameless hiding (name,Infix,Val,Con,Equal,Refl)
-- import Text.Parsec hiding (ParseError,Empty)
-- import Text.Parsec.Error(errorMessages, messageString)
-- import qualified Text.Parsec as P
-- import Text.Parsec.Language
-- import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
-- import qualified Text.Parsec.Token as Token
-- import Data.Typeable
-- import Control.Applicative hiding ((<|>),many)
-- import "mtl" Control.Monad.Identity
-- import Control.Exception(Exception)
-- import Data.Char
-- import Text.PrettyPrint(render)


symbol :: Parser Char
 symbol = oneOf "!#$%&|*+-/:<=>?@^_~"
