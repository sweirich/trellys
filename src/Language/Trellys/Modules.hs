{-# LANGUAGE FlexibleContexts #-}
module Language.Trellys.Modules(getModules) where

import Language.Trellys.Syntax
import Language.Trellys.Parser(parseModuleFile)


import Language.Trellys.GenericBind

import Text.ParserCombinators.Parsec.Error
import Control.Monad.Error
import System.FilePath
import System.Directory
import System.Environment(getEnv)
import System.IO.Error(isDoesNotExistError)
import qualified Data.Graph as Gr
import Data.List(nub,(\\))

-- | getModules starts with a top-level module, and gathers all of the module's
-- transitive dependency. It returns the list of parsed modules, with all
-- modules appearing after its dependencies.
getModules
  :: (MonadIO m) => String -> m (Either ParseError [Module])
getModules top = runErrorT $ gatherModules [string2Name top] []

-- | Build the module dependency graph, with parsed modules.
gatherModules
  :: (MonadError ParseError m, MonadIO m) =>
     [Name] -> [Module] -> m [Module]
gatherModules [] accum = return $ topSort accum
gatherModules (m:ms) accum = do
  modFileName <- getModuleFileName m
  parsedMod <- parseModule modFileName
  let accum' = parsedMod:accum
  let oldMods = map moduleName accum'
  let newMods = [mn | ModuleImport mn <- moduleImports parsedMod]
  gatherModules (nub (ms ++ newMods) \\ oldMods) accum'


-- | Generate a sorted list of modules, with the postcondition that a module
-- will appear _after_ any of its dependencies.
-- topSort :: [Module] -> [Module]
topSort :: [Module] -> [Module]
topSort ms = reverse sorted -- gr -- reverse $ topSort' ms []
  where (gr,lu) = Gr.graphFromEdges' [(m, moduleName m, [i | ModuleImport i <- moduleImports m])
                                      | m <- ms]
        lu' v = let (m,_,_) = lu v in m
        sorted = [lu' v | v <- Gr.topSort gr]



instance Error ParseError

-- | Find the file associated with a module. Currently very simple.
--  We look for files corresponding to module 'm' in the following order:
getModuleFileName :: (MonadIO m, Show a) => a -> m String
getModuleFileName m = do
  sp <- liftIO $ getIncludePaths
  checkMods [base </> c <.> ext | base <- sp, c <- candidates, ext <- extensions]

  where hierName = joinPath $ splitString '.' (show m)
        candidates = [show m, hierName]
        extensions = ["","trellys","tys"]
        -- Probe for names
        checkMods [] = fail $ "Could not find module " ++ show m
        checkMods (c:cs) = do fe <- liftIO $ doesFileExist c
                              liftIO $ putStrLn $ "Checking for " ++ c
                              if fe
                                 then return c
                                 else checkMods cs


-- | Return a list of directories to search when looking for a module file.
getIncludePaths :: IO [String]
getIncludePaths = do str <- getEnv "TRELLYS_INCLUDE"
                     return $ splitString ':' str
     `catch`
     (\e -> if isDoesNotExistError e then return ["."] else ioError e)



-- | Split a string based on a given character.
splitString :: Char -> String -> [String]
splitString delim s =
  case s' of
    [] -> [l]
    (_:rest) -> l : splitString delim rest
  where (l,s') = break (== delim) s

parseModule
  :: (MonadIO m, MonadError ParseError m) => String -> m Module
parseModule fname = do
  res <- liftIO $ parseModuleFile fname
  case res of
    Left err -> throwError err
    Right v -> return v


