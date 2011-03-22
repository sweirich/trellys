module Language.Trellys.Options where

import System.Environment(getArgs)
import System.Console.GetOpt

-- Options handling stuff. To be determined.
options :: [OptDescr Flag]
options = [Option "t" ["typecheck"] (NoArg TypeCheck) "Typecheck the module", 
           Option "p" ["picky equality"] (NoArg PickyEq) "Use strongly typed equality",
           Option "e" ["elaborate"] (NoArg Elaborate) "elaborate into core language",
           Option "r" ["reduce"] (NoArg Reduce) "reduce the last term in the module"
          ]

data Flag = TypeCheck
          | Parse
          | PickyEq
          | Elaborate
          | Reduce
  deriving (Eq,Show,Read)
