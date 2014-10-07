{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.Modules(getModules, writeAModules) where

import Language.Trellys.Options
import Language.Trellys.Syntax
import Language.Trellys.Parser(parseModuleFile, parseModuleImports)
import Language.Trellys.PrettyPrint
import Language.Trellys.GenericBind

import Prelude hiding (mod)
import Text.PrettyPrint.HughesPJ (render)
import Text.ParserCombinators.Parsec.Error
import Control.Applicative 
import Control.Monad.Error
import Control.Monad.State.Lazy
import System.FilePath
import System.Directory
import Data.Binary (Binary, encode, decode)
import qualified Data.Binary as Bin
import Data.Binary.Get (isEmpty)
import qualified Data.ByteString.Lazy as BS
import System.Posix.Files (fileExist, getFileStatus, modificationTime)
import qualified Data.Graph as Gr
import Data.List(nub,(\\))

-- | getModules starts with a top-level module, and gathers all of the module's
-- transitive dependency. It returns the list of parsed modules, with all
-- modules appearing after its dependencies.
-- 
-- If there is a pre-compiled binary version of module (.trellys-bin) which was written
-- after the .trellys file, we return that one instead.
getModules
  :: (Functor m, MonadError ParseError m, MonadIO m) => 
     [Flag] -> [FilePath] -> String -> m [Either Module AModule]
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
gatherModules flags  prefixes mods = gatherModules' mods [] where
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

-- | Is the .trellys-bin file up to date?
isBinCurrent :: FilePath -> IO Bool
isBinCurrent basename = do
  exists1 <- fileExist (basename)
  exists2 <- fileExist (basename ++ "-bin")
  if not (exists1 && exists2)
     then return False
     else do 
            status1 <- getFileStatus basename
            status2 <- getFileStatus (basename ++ "-bin")
            return $ modificationTime status1 < modificationTime status2
  

-- | Fully parse a module (not just the imports).
reparse :: (MonadError ParseError m, MonadIO m, MonadState ConstructorNames m, Functor m) => 
            [Flag] -> ModuleInfo -> m (Either Module AModule)
reparse flags (ModuleInfo _ fileName _) = do
  current <- liftIO $ isBinCurrent fileName
  if current 
    then Right <$> reparseBinary fileName
    else Left  <$> reparseSource flags fileName

reparseSource :: (MonadError ParseError m, MonadIO m, MonadState ConstructorNames m) => 
            [Flag] -> FilePath -> m Module
reparseSource flags fileName = do
  liftIO $ putStrLn $ "Parsing source file " ++ show fileName
  cnames <- get
  mod <- parseModuleFile flags cnames fileName
  modify (cnamesUnion (moduleConstructors mod))
  return mod

reparseBinary :: (MonadError ParseError m, MonadIO m, MonadState ConstructorNames m, Functor m) => 
                 FilePath -> m AModule
reparseBinary fileName = do
  liftIO $ putStrLn $ "Parsing binary file " ++ show (fileName++"-bin")
  amod <- fromEOFTerminated . decode <$> liftIO (BS.readFile (fileName++"-bin"))
  modify (cnamesUnion (aModuleConstructors amod))
  return amod

writeAModules :: MonadIO m => [FilePath] -> [AModule] -> m ()
writeAModules prefixes mods = mapM_ (writeAModule prefixes) mods

writeAModule :: MonadIO m => [FilePath] -> AModule -> m ()
writeAModule prefixes mod = do
  basename <- getModuleFileName prefixes (aModuleName mod)
  liftIO $ BS.writeFile (basename ++ "-bin") (encode mod)
  liftIO $ writeFile (basename ++ "-elaborated") (render $ disp mod)  


-- Hack to ensure that the lazy ByteString gets closed. 
newtype EOFTerminated a = EOFTerminated { fromEOFTerminated :: a }
instance Binary a => Binary (EOFTerminated a) where
  put (EOFTerminated x) = Bin.put x
  get = do x <- Bin.get
           end <- isEmpty
           unless end $ error "expected EOF when parsing .trellys-bin file"
           return (EOFTerminated x)