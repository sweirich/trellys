{-# LANGUAGE FlexibleContexts #-}
module Trellys where


import Language.Trellys.Modules
import Language.Trellys.PrettyPrint
import Language.Trellys.TypeCheck
import Control.Monad.Reader

import Text.PrettyPrint.HughesPJ(render)
import Text.ParserCombinators.Parsec.Error

import System.Environment(getArgs)
import System.Console.GetOpt
import System.Exit

main :: IO ()
main = do
  -- FIXME: This currently requires exactly one module. This should be fixed to
  -- allow multiple modules to be passed in, perhaps using command line flags.
  (flags,[rest]) <- getArgs >>= getOptions
  putStrLn "Trellys main"
  res <- getModules rest
  -- ast <- parseModuleFile rest
  case res of
    Left parseError -> do
             putStrLn $ render $ disp $ errorPos parseError
             putStrLn $ show parseError
             exitFailure
    Right val -> do
             when (TypeCheck `elem` flags) $ do
               putStrLn "TypeChecking"
               contents <- runTcMonad emptyEnv (tcModules val)
               case contents of
                 Left typeError -> do
                          putStrLn "Type Error:"
                          putStrLn $ render $ disp typeError
                          exitFailure
                 Right _ -> do
                          putStrLn "Type check successful" -- putStrLn $ render $ disp defs


getOptions :: [String] -> IO ([Flag], [String])
getOptions argv =
       case getOpt Permute options argv of
          (o,n,[]  ) -> return (o,n)
          (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
      where header = "Usage: trellys [OPTION...] files..."

-- Options handling stuff. To be determined.
options :: [OptDescr Flag]
options = [Option "t" ["typecheck"] (NoArg TypeCheck) "Typecheck the module"
          ]


data Flag = TypeCheck
          | Parse
  deriving (Eq,Show,Read)

