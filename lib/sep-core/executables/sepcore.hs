module Main where
import Language.SepCore.Parser
import Language.SepCore.Lexer
import Language.SepCore.Syntax
import Language.SepCore.Typecheck
import Unbound.LocallyNameless
import Text.PrettyPrint(render)
import System.Console.CmdArgs
import Data.Typeable
import Control.Exception
import Control.Monad.State
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import System.Environment
import Data.Map

main = do
  args <- getArgs
  case args of
    [filename] -> do
      cnts <- readFile filename;
      case runAlex cnts parser of
             Left e -> error e
             Right a -> do putStrLn $ "Parsing success! \n" ++(show a)
                           s <- runFreshMT (evalStateT (typechecker a) Data.Map.empty)
                           print s


    _ -> putStrLn "usage: sepcore <filename>"
