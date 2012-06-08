module BaseTypes where

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$),render)

data Base = Int | Char | Double | Integer | Unit
  deriving Eq

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

litToBase (LInt n) = Int
litToBase (LInteger n) = Integer
litToBase (LDouble n) = Double
litToBase (LChar c) = Char
litToBase LUnit = Unit  


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
  
  
-- Base 
instance Show Base where
  show Int = "Int"
  show Char = "Char"
  show Double = "Double"
  show Integer = "Integer"
  show Unit = "()"


