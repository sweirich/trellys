module BaseTypes where

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

data Literal 
   = LInt Int                  -- 5 , -5
   | LDouble Double            -- 2.3 , 0.5 , -3.4
   | LChar Char                -- 'x'
   | LInteger Integer
   | LUnit

instance Eq Literal where
  (LInt n) == (LInt m) = n==m
  (LInteger n) == (LInteger m) = n==m
  (LDouble n) == (LDouble m) = n==m
  (LChar n) == (LChar m) = n==m
  LUnit == LUnit = True
  _ == _ = False

typeNameLit (LInt n) = "Int"
typeNameLit (LInteger n) = "Integer"
typeNameLit (LDouble n) = "Double"
typeNameLit (LChar c) = "Char"
typeNameLit LUnit = "()"

ppLit :: Literal -> Doc
ppLit (LInt n) = text(show n)
ppLit (LInteger n) = text(show n)
ppLit (LDouble d) = text (show d)
ppLit (LChar c) = text(show c)
ppLit (LUnit) = text "()"
