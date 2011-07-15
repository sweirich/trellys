{-# LANGUAGE FlexibleContexts #-}
module Language.Trellys.Modules(getModules, writeModules) where

import Language.Trellys.Syntax
import Language.Trellys.Parser(parseModuleFile)

import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ (render)

import Language.Trellys.GenericBind

import Text.ParserCombinators.Parsec.Error
import Control.Monad.Error
import System.FilePath
import System.Directory
import qualified Data.Graph as Gr
import Data.List(nub,(\\))

-- | getModules starts with a top-level module, and gathers all of the module's
-- transitive dependency. It returns the list of parsed modules, with all
-- modules appearing after its dependencies.
getModules
  :: (MonadIO m) => [FilePath] -> String -> m (Either ParseError [Module])
getModules prefixes top = runErrorT $ gatherModules prefixes [string2Name top]

-- | Build the module dependency graph, with parsed modules.
gatherModules
  :: (MonadError ParseError m, MonadIO m) =>
     [FilePath] -> [MName] -> m [Module]
gatherModules prefixes ms = gatherModules' ms [] where
  gatherModules' [] accum = return $ topSort accum
  gatherModules' (m:ms) accum = do
    modFileName <- getModuleFileName prefixes m
    parsedMod <- parseModule modFileName
    let accum' = parsedMod:accum
    let oldMods = map moduleName accum'
    let newMods = [mn | ModuleImport mn <- moduleImports parsedMod]
    gatherModules' (nub (ms ++ newMods) \\ oldMods) accum'


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

-- | Find the file associated with a module.
getModuleFileName :: (MonadIO m, Show a)
                  => [FilePath] -> a -> m FilePath
getModuleFileName prefixes mod = do
  let makeFileName prefix = prefix </> mDotTrellys
      -- get M.trellys from M or M.trellys
      mDotTrellys = if takeExtension s == ".trellys"
                    then s
                    else s <.> "trellys"
      s = show mod
      possibleFiles = map makeFileName prefixes
  files <- liftIO $ filterM doesFileExist possibleFiles
  if null files
     then error $ "Can't locate module: " ++ show mod ++
                "\nTried: " ++ show possibleFiles
     else return $ head files

parseModule
  :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModule fname = do
  res <- liftIO $ parseModuleFile fname
  case res of
    Left err -> throwError err
    Right v -> return v

writeModules :: MonadIO m => [FilePath] -> [Module] -> m ()
writeModules prefixes mods = mapM_ (writeModule prefixes) mods

writeModule :: MonadIO m => [FilePath] -> Module -> m ()
writeModule prefixes mod = do
  basename <- getModuleFileName prefixes (moduleName mod)
  liftIO $ writeFile (basename ++ "-elaborated") (render $ disp mod)  
