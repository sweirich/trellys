{-# LANGUAGE FlexibleContexts #-}
module Trellys where

import Language.Trellys.Options
import Language.Trellys.Syntax (moduleEntries)
import Language.Trellys.Modules
import Language.Trellys.PrettyPrint
import Language.Trellys.TypeCheck
import Language.Trellys.OpSem
import Language.Trellys.Environment
import Control.Monad.Reader

import Text.PrettyPrint.HughesPJ (render, text, fsep)
import Text.ParserCombinators.Parsec.Error

import System.Environment(getArgs)
import System.Console.GetOpt
import System.Exit
import System.FilePath (splitFileName)

import Data.List (delete)

main :: IO ()
main = do
  -- FIXME: This currently requires exactly one module. This should be fixed to
  -- allow multiple modules to be passed in, perhaps using command line flags.
  (flags, [pathToMainFile]) <- getOptions =<< getArgs
  let prefixes = currentDir : mainFilePrefix : [dir | LibDir dir <- flags]
      (mainFilePrefix, name) = splitFileName pathToMainFile
      currentDir = ""
  putStrLn "Trellys main"
  res <- getModules prefixes name
  -- ast <- parseModuleFile rest
  case res of
    Left parseError -> do
             putStrLn $ render $ disp $ errorPos parseError
             putStrLn $ show parseError
             exitFailure
    Right val -> do
             putStrLn "TypeChecking"
             contents <- runTcMonad (emptyEnv flags) (tcModules val)
             case contents of
               Left typeError -> do
                        putStrLn "Type Error:"
                        putStrLn $ render $ disp typeError
                        exitFailure
               Right defs ->
                 if (Elaborate `elem` flags)
                   then do
                        putStrLn "Elaboration pass successful. Typechecking the core terms."
                        --writeModules defs --can uncomment this line for debugging.
                        contents' <- runTcMonad (emptyEnv (delete Elaborate flags)) (tcModules defs)
                        case contents' of
                          Left typeError -> do
                                  putStrLn "Internal error, elaborated term fails type check:"
                                  putStrLn $ render $ disp typeError
                                  exitFailure
                          Right _ -> do
                            putStrLn "Type check successful. Writing elaborated terms."
                            writeModules prefixes defs

                   else do
                        putStrLn "Type check successful"
                        if (Reduce `elem` flags)
                           then do
                              let eenv = concatMap makeModuleEnv defs
                              -- print defs -- comment out for debuggging
                              r <- runTcMonad
                                     (emptyEnv flags)
                                     (extendCtxs (concatMap moduleEntries defs)
                                        (cbvNSteps 100 =<< erase
                                                       =<< substDefs (snd $ last eenv)))
                              case r of
                                Left err -> do putStrLn "Reduce Error:"
                                               putStrLn $ render $ disp err
                                Right x -> putStrLn $ render $ disp x
                           else return ()


getOptions :: [String] -> IO ([Flag], [String])
getOptions argv =
       case getOpt Permute options argv of
          (o,n,[]  ) -> return (o,n)
          (_,_,errs) -> ioError $ userError $ concat errs
                                  ++ usageInfo header options
                                  ++ "\n" ++ footer
      where header = "Usage: trellys [OPTION...] FILE"
            -- fill argument string (as paragraph) to 100 columns
            paragraphFill = render . fsep . map text . words
            footer = "How modules are located:"

                     ++ "\n\n" ++ paragraphFill
                     "Modules are searched for (in order) in the current directory, \
                     \the directory containing FILE, and in all directories DIR specified \
                     \with --lib DIR options.  The first file found, whose name matches the \
                     \searched for module name, is used."

                     ++ "\n\n" ++ paragraphFill
                     "The --elaborate option requires \
                     \that the files M.trellys begins with \"module M where\"."

                     ++ "\n\n" ++ paragraphFill
                     "The main module FILE can be a file name ending in \".trellys\", \
                     \or a plain module name."
