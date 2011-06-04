{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Language.SepPP.Parser
import Language.SepPP.PrettyPrint
import Language.SepPP.TypeCheck
import Language.SepPP.Syntax(Term(..),var,app,Stage(..))
import Unbound.LocallyNameless(Embed(..),bind,string2Name)

import Text.PrettyPrint(render)

import System.Console.CmdArgs
import Data.Typeable
import Control.Exception
import System.Environment
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)

main = do
  opts <- cmdArgs sepPPArgs
  -- cnts <- withFile (file opts) ReadMode hGetContents            
  bracket (openFile (file opts)ReadMode ) hClose $ \ h ->
     do cnts <- hGetContents h
  -- Parse the module
        ast <- liftEither $  parseModule (file opts) cnts
        dast <- display ast

  -- Typecheck the module
        tcres <- typecheck ast
        case tcres of
         Left err -> fail $ runDisp err
         Right val -> return ()


  -- _ <- liftEither tcres

        putStrLn "Success!"


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


go s = withArgs ["--file="++s] main

testcase = "../Tests/unittests/ParseTest.sepp"


--------------------------------------

less1 = IndLT (var "x") (var "y")
eq1 = Equal (var "x") (var "y")

test p s =  putStrLn(runDisp (parse2 p s))
