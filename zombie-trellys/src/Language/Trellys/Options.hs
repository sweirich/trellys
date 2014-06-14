module Language.Trellys.Options where

import System.Environment(getArgs)
import System.Console.GetOpt

-- Options handling stuff. To be determined.
options :: [OptDescr Flag]
options = [Option "r" ["reduce"] (NoArg Reduce) "reduce the last term in the module",
           Option "L" ["lib"] (ReqArg LibDir "DIR") "look for imports in DIR (this option can be supplied multiple times)",
           Option "n" ["nocoercions"] (NoArg NoCoercions) "do not automatically infer equality proofs",
           Option ""  ["no-tc-core"] (NoArg NoTypeCheckCore) "suppress type checking the core language", 
           Option "" ["typeclassy"] (NoArg Typeclassy) "enable some ad hoc typeclass hackery",
           Option "e" ["extraction"] (NoArg DoExtraction) "extract to OCaml code",
           Option "" ["no-injrng"] (NoArg NoInjrngCheck) "disable the injrng check"
          ]

data Flag = NoTypeCheckCore
          | NoCoercions
          | Reduce
          | LibDir FilePath
          | DoExtraction
          | Typeclassy
          | NoInjrngCheck
          | SecondPass   --used internally, when we re-check the elaborated core term. 
  deriving (Eq,Show,Read)
