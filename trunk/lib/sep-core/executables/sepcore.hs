module Main where
import Language.SepCore.Parser
import Language.SepCore.Lexer
import Language.SepCore.Syntax
import Unbound.LocallyNameless(Embed(..),bind,string2Name)
import Text.PrettyPrint(render)
import System.Console.CmdArgs
import Data.Typeable
import Control.Exception
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import System.Environment


main = do
  args <- getArgs
  case args of
    [filename] -> do
      cnts <- readFile filename;
      case runAlex cnts parser of
             Left e -> error e
             Right a ->putStrLn $ "Parsing success! \n" ++(show a)

    _ -> putStrLn "usage: sepcore <filename>"
