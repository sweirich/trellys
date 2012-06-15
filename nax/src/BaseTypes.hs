module BaseTypes
  ( Literal(..)
  , ppLit
  ) where

import Text.PrettyPrint.HughesPJ (Doc,text)

data Literal 
   = LInt Int
   | LDouble Double
   | LChar Char
   | LInteger Integer
   | LUnit
   deriving Eq

ppLit :: Literal -> Doc
ppLit (LInt n) = text(show n)
ppLit (LInteger n) = text(show n)
ppLit (LDouble d) = text (show d)
ppLit (LChar c) = text(show c)
ppLit (LUnit) = text "()"
