module Language.SepCore.Rewriting where
import Language.SepCore.Erasure
import Language.SepCore.Syntax
import Language.SepCore.PrettyPrint

import Generics.RepLib hiding (Con(..))
import Unbound.LocallyNameless hiding (Con(..),Equal,Refl)
import Control.Monad.Trans
import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Text.PrettyPrint(render, text,(<+>),($$))


isNormalForm :: ETerm -> m Bool
isNormalForm (ETermVar x) = return True
isNormalForm (EType i) = return True
isNormalForm (EPi binding s) = do 
  ((x,Embed t'), t) <- unbind binding
  isNormalForm t'

isNormalForm (ELambda b) = return True
isNormalForm (ERec b) = return True
isNormalForm (EAbort) = return True
isNormalForm (EApp (ETermVar x) t2) = isNormalForm t2
isNormalForm _ = return False


join t1 t2 = 


