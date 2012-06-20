{-# LANGUAGE DeriveDataTypeable, PackageImports, FlexibleContexts #-}

module Language.SepPP.Options where

import System.Console.CmdArgs
import qualified Data.Map as M
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error



data SepPPOpts = SepPPOpts {
    file :: String
  } deriving (Show,Read,Eq,Typeable,Data)

sepPPArgs :: SepPPOpts
sepPPArgs = SepPPOpts {
              file = def
                     &= help "Input file" &=
                     groupname "Main"
            }

-- FIXME: This should be calculated from sepPPArgs
flags :: [(String,Bool)]
flags = [("ShowReductions", False)
        ,("DisableValueRestriction", False)
        ,("ImplicitArgs", False)
        ,("PrintAST", False)
        ]
flagMap :: M.Map String Bool
flagMap = M.fromList flags

type Flags = M.Map String Bool


-- Handling flags

setFlag :: (MonadState (M.Map String Bool) m) => String -> Bool -> m ()
setFlag n val = modify (M.insert n val)

getFlag :: (Error e, MonadError e m, MonadState (M.Map String Bool) m) => String -> m Bool
getFlag n = do
  opts <- get
  case M.lookup n opts of
   Just b -> return b
   Nothing -> throwError $ strMsg $ "Could not find flag " ++ n ++ show opts


getOptShowReductions, getOptDisableValueRestriction, getOptImplicitArgs, getOptPrintAST ::
  (Error e, MonadError e m, MonadState Flags m) => m Bool
getOptShowReductions = getFlag "ShowReductions"
getOptDisableValueRestriction = getFlag "DisableValueRestriction"
getOptImplicitArgs = getFlag "ImplicitArgs"
getOptPrintAST = getFlag "PrintAST"