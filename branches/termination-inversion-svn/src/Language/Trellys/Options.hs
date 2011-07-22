module Language.Trellys.Options where

import System.Environment(getArgs)
import System.Console.GetOpt

-- Options handling stuff. To be determined.
options :: [OptDescr Flag]
options = [Option "t" ["typecheck"] (NoArg TypeCheck) "typecheck the module",
           Option "p" ["picky equality"] (NoArg PickyEq) "use strongly typed equality",
           Option "e" ["elaborate"] (NoArg Elaborate) "elaborate into core language",
           Option "r" ["reduce"] (NoArg Reduce) "reduce the last term in the module",
           Option "L" ["lib"] (ReqArg LibDir "DIR") "look for imports in DIR (this option can be supplied multiple times)"
          ]

data Flag = TypeCheck
          | Parse
          | PickyEq
          | Elaborate
          | Reduce
          | LibDir FilePath
  deriving (Eq,Show,Read)
