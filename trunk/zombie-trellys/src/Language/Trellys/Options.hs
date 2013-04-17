module Language.Trellys.Options where

import System.Environment(getArgs)
import System.Console.GetOpt

-- Options handling stuff. To be determined.
options :: [OptDescr Flag]
options = [Option "p" ["picky equality"] (NoArg PickyEq) "use strongly typed equality",
           Option "r" ["reduce"] (NoArg Reduce) "reduce the last term in the module",
           Option "L" ["lib"] (ReqArg LibDir "DIR") "look for imports in DIR (this option can be supplied multiple times)",
           Option "n" ["nocoercions"] (NoArg NoCoercions) "do not automatically infer equality proofs",
           Option ""  ["parallel"] (NoArg UseParallelReduction) "use parallel (rather than CBV) reduction for join"
          ]

data Flag = PickyEq
          | NoCoercions
          | Reduce
          | LibDir FilePath
          | UseParallelReduction
          | SecondPass   --used internally, when we re-check the elaborated core term. 
  deriving (Eq,Show,Read)
