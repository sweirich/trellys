{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}
module Main where

import Language.SepPP.Parser
import Language.SepPP.PrettyPrint
import Language.SepPP.TypeCheck
import Language.SepPP.TCUtils(TypeError(ErrMsg))
import Language.SepPP.Syntax(Term(..),var,app,Stage(..))
import Unbound.LocallyNameless(Embed(..),bind,string2Name)

import Text.PrettyPrint(render)
import Text.Parsec(ParseError)

import System.Console.CmdArgs
import Data.Typeable
import Control.Exception
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)

main = flip catches handlers $ do
  opts <- cmdArgs sepPPArgs
  -- cnts <- withFile (file opts) ReadMode hGetContents
  bracket (openFile (file opts)ReadMode ) hClose $ \ h ->
     do cnts <- hGetContents h
  -- Parse the module
        ast <- liftEither $  parseModule (file opts) cnts

  -- Typecheck the module
        tcres <- typecheck ast
        liftEither tcres
        putStrLn "Success!"
        exitSuccess

  where handlers = [Handler parseHandler, Handler typeHandler]
        typeHandler e@(ErrMsg _) = print (disp e) >> exitFailure
        parseHandler (e :: ParseError)= print (disp e) >> exitFailure




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


go s = handle h $ withArgs ["--file="++s] main
  where h e@(ErrMsg _) = do
          print $ disp e

testcase = "Tests/unittests/ParseTest.sepp"
testcase2 = "Tests/unittests/IndVRDemo.sepp"
--------------------------------------

less1 = IndLT (var "x") (var "y")
eq1 = Equal (var "x") (var "y")

test p s =  print (disp (parse2 p s))
