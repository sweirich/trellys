module Language.Trellys.Options where

import System.Environment(getArgs)
import System.Console.GetOpt

-- Options handling stuff. To be determined.
options :: [OptDescr Flag]
options = [Option "p" ["picky equality"] (NoArg PickyEq) "use strongly typed equality",
           Option "r" ["reduce"] (NoArg Reduce) "reduce the last term in the module",
           Option "L" ["lib"] (ReqArg LibDir "DIR") "look for imports in DIR (this option can be supplied multiple times)",
           Option "n" ["nocoercions"] (NoArg NoCoercions) "do not automatically infer equality proofs",
           Option ""  ["no-tc-core"] (NoArg NoTypeCheckCore) "suppress type checking the core language", 
           Option ""  ["non-logical-types"] (NoArg NonLogicalTypes) 
                         "do not force all types to be logical",
           Option "" ["typeclassy"] (NoArg Typeclassy) "enable some ad hoc typeclass hackery",
           Option "e" ["extraction"] (NoArg DoExtraction) "extract to OCaml code"
          ]

data Flag = PickyEq
          | NoTypeCheckCore
          | NoCoercions
          | Reduce
          | LibDir FilePath
          | NonLogicalTypes
          | DoExtraction
          | Typeclassy
          | SecondPass   --used internally, when we re-check the elaborated core term. 
  deriving (Eq,Show,Read)
