{-# LANGUAGE DeriveDataTypeable, PackageImports, FlexibleContexts #-}

module Language.SepPP.Options where

import System.Console.CmdArgs
import Data.Typeable
import qualified Data.Map as M
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error



data SepPPOpts = SepPPOpts {
    file :: String
  } deriving (Show,Read,Eq,Typeable,Data)

sepPPArgs = SepPPOpts {
              file = def
                     &= help "Input file" &=
                     groupname "Main"
            }

-- FIXME: This should be calculated from sepPPArgs
flags = [("ShowReductions", False)
        ,("DisableValueRestriction", False)
        ]
flagMap = M.fromList flags

type Flags = M.Map String Bool


-- Handling flags
setFlag n val = modify (M.insert n val)
getFlag n = do
  opts <- get
  case M.lookup n opts of
   Just b -> return b
   Nothing -> throwError $ strMsg $ "Could not find flag " ++ n ++ show opts


getOptShowReductions, getOptDisableValueRestriction ::
  (Error e, MonadError e m, MonadState Flags m) => m Bool
getOptShowReductions = getFlag "ShowReductions"
getOptDisableValueRestriction = getFlag "DisableValueRestriction"