module Main where

import Language.SepPP.Parser
import Language.SepPP.PrettyPrint
import Language.SepPP.TypeCheck


import System.Console.CmdArgs
import Data.Typeable
import Control.Exception

main = do
  opts <- cmdArgs sepPPArgs
  cnts <- readFile (file opts)
  -- Parse the module
  ast <- liftEither $  parseModule (file opts) cnts
  dast <- display ast

  -- Typecheck the module
  tcres <- typecheck ast
  _ <- liftEither tcres

  print dast


data SepPPOpts = SepPPOpts {
    file :: String
  } deriving (Show,Read,Eq,Typeable,Data)


sepPPArgs = SepPPOpts {
              file = def
                     &= help "Input file" &=
                     groupname "Main"
            }

-- liftEither :: Exception a => Either a b -> IO b
liftEither (Left err) = throw err
liftEither (Right val) = return val