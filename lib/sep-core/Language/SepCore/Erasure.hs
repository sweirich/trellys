module Language.SepCore.Erasure where 
import Language.SepCore.Syntax
import Language.SepCore.Lexer
import Language.SepCore.PrettyPrint
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Alpha(aeqR1)
import Unbound.LocallyNameless.Subst(substR1)
import Text.PrettyPrint

data ETerm =  ETermVar (Name ETerm)

           | EType Integer

           | EPi (Bind (ArgName, Embed ArgClass) ETerm) Stage

           | ETermLambda (Bind ArgName ETerm) Stage
                                 
           | ELet (Bind (Name ETerm) ETerm) ETerm

           | ECase ETerm ETermBranches

           | ETcast ETerm 

           | EApp ETerm ETerm

           | EAbort

           | ERec (Bind (Name ETerm, Name ETerm) ETerm)
           
--bind two term in a term.

  deriving(Show)

$(derive [''ETerm])