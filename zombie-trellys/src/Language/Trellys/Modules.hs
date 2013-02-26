{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.Modules(getModules, writeAModules) where

import Language.Trellys.Options
import Language.Trellys.Syntax
import Language.Trellys.Parser(parseModuleFile, parseModuleImports)

import Language.Trellys.PrettyPrint
import Text.PrettyPrint.HughesPJ (render)

import Language.Trellys.GenericBind

import Text.ParserCombinators.Parsec.Error
import Control.Applicative 
import Control.Monad.Error
import Control.Monad.State.Lazy
import System.FilePath
import System.Directory
import qualified Data.Graph as Gr
import Data.List(nub,(\\))

-- | getModules starts with a top-level module, and gathers all of the module's
-- transitive dependency. It returns the list of parsed modules, with all
-- modules appearing after its dependencies.
getModules
  :: (Functor m, MonadError ParseError m, MonadIO m) => 
     [Flag] -> [FilePath] -> String -> m [Module]
getModules flags prefixes top = do
  toParse <- gatherModules flags prefixes [ModuleImport $ string2Name top]
  flip evalStateT emptyConstructorNames $
    mapM (reparse flags) toParse

data ModuleInfo = ModuleInfo {
                    modInfoName :: MName, 
                    modInfoFilename :: String,
                    modInfoImports :: [ModuleImport]
                  }

-- | Build the module dependency graph.
--   This only parses the imports part of each file; later we go back and parse all of it.
gatherModules
  :: (Functor m, MonadError ParseError m, MonadIO m) =>
     [Flag]  -> [FilePath] -> [ModuleImport] -> m [ModuleInfo]
gatherModules flags  prefixes ms = gatherModules' ms [] where
  gatherModules' [] accum = return $ topSort accum
  gatherModules' ((ModuleImport m):ms) accum = do
    modFileName <- getModuleFileName prefixes m
    imports <- moduleImports <$> parseModuleImports flags modFileName
    let accum' = (ModuleInfo m modFileName imports) :accum
    let oldMods = map (ModuleImport . modInfoName) accum'
    gatherModules' (nub (ms ++ imports) \\ oldMods) accum'

-- | Generate a sorted list of modules, with the postcondition that a module
-- will appear _after_ any of its dependencies.
-- topSort :: [Module] -> [Module]
topSort :: [ModuleInfo] -> [ModuleInfo]
topSort ms = reverse sorted -- gr -- reverse $ topSort' ms []
  where (gr,lu) = Gr.graphFromEdges' [(m, modInfoName m, [i | ModuleImport i <- modInfoImports m])
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

-- | Fully parse a module (not just the imports).
reparse :: (MonadError ParseError m, MonadIO m, MonadState ConstructorNames m) => 
            [Flag] -> ModuleInfo -> m Module
reparse flags (ModuleInfo _ fileName _) = do
  cnames <- get
  mod <- parseModuleFile flags cnames fileName
  put (moduleConstructors mod)
  return mod

writeAModules :: MonadIO m => [FilePath] -> [AModule] -> m ()
writeAModules prefixes mods = mapM_ (writeAModule prefixes) mods

writeAModule :: MonadIO m => [FilePath] -> AModule -> m ()
writeAModule prefixes mod = do
  basename <- getModuleFileName prefixes (aModuleName mod)
  liftIO $ writeFile (basename ++ "-elaborated") (render $ disp mod)  
