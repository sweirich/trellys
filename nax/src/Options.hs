{-# LANGUAGE DeriveDataTypeable #-}

-- Based on https://github.com/cpa/haskellcontracts/blob/master/src/Options.hs
module Options where

import System.Console.CmdArgs

data Conf = Conf
  { interactive :: Bool
  , file        :: FilePath
  }
  deriving (Data, Typeable)

defaultConf = Conf
  { interactive = False
  , file = error "FILE is undefined."
  }

getOpts = cmdArgs $ Conf 
  { interactive = def
    &= help "Start interpreter after type checking FILE."

  , file = def
    &= argPos 0 -- A positional, not named switch, argument.
    &= typFile
  } &= 
  verbosity &=
  program "nax" &=
  helpArg [explicit, name "h", name "help"] &= -- Avoid stupid '-?' default switch.
  summary "Nax, V 1/0" &=
  details
  [ "Default behavior is to typecheck FILE." ]

