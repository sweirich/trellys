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
  :: (MonadIO m) => String -> m (Either ParseError [Module])
getModules top = runErrorT $ gatherModules [string2Name top] []

-- | Build the module dependency graph, with parsed modules.
gatherModules
  :: (MonadError ParseError m, MonadIO m) =>
     [MName] -> [Module] -> m [Module]
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
getModuleFileName :: (MonadIO m, Show a) => a -> m String
getModuleFileName m = do
  fe <- liftIO $ doesFileExist (show m)
  if fe
     then return (show m)
     else return (addExtension (show m) "trellys")
          -- TODO: Add support for tys extension.


parseModule
  :: (MonadIO m, MonadError ParseError m) => String -> m Module
parseModule fname = do
  res <- liftIO $ parseModuleFile fname
  case res of
    Left err -> throwError err
    Right v -> return v

writeModules :: MonadIO m => [Module] -> m ()
writeModules mods = mapM_ writeModule mods

writeModule :: MonadIO m => Module -> m ()
writeModule mod = do
  basename <- getModuleFileName (moduleName mod)
  liftIO $ writeFile (basename ++ "-elaborated") (render $ disp mod)  
