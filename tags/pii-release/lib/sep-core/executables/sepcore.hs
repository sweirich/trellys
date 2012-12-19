module Main where
import Language.SepCore.Parser
import Language.SepCore.Lexer
import Language.SepCore.Syntax
import Language.SepCore.Typecheck2
import Language.SepCore.PrettyPrint
import Control.Monad.Error hiding (join)
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
             Right a -> do putStrLn $ "Parsing success! \n" 
                           unknow <- runErrorT (runFreshMT (runStateT (typechecker a) (Data.Map.empty,Data.Map.empty)))
                           case unknow of
                             Left e -> do
                               putStrLn $ show (disp e)
                             Right (s,env) -> do
                               putStrLn $ show (disp s) ++ "\n"
                               putStrLn $ show (disp (fst env)) ++ "\n"
                               putStrLn $ show (disp (snd env))


                           
                           


    _ -> putStrLn "usage: sepcore <filename>"
