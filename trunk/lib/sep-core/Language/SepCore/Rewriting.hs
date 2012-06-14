module Language.SepCore.Rewriting where
import Language.SepCore.Erasure
import Language.SepCore.Syntax
import Language.SepCore.PrettyPrint
import Language.SepCore.Monad
import Language.SepCore.Error
import Generics.RepLib hiding (Con(..))
import Control.Monad.Reader hiding (join)
import Unbound.LocallyNameless hiding (Con(..),Equal,Refl)
import Control.Monad.Trans
import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Data.List
import Text.PrettyPrint(render, text,(<+>),($$))
import qualified Data.Map as M


--type Trace = StateT [ETerm] (FreshMT (ErrorT TypeError IO))

-- | val t judgement
isValue :: ETerm -> TCMonad Bool

isValue (ETermVar x) = do
  v <- getValue (ArgNameTerm (translate x))
  case v of
    Value ->
         return True
    NonValue -> return False

isValue (EType i) = return True

isValue (EPi binding s) = do 
  ((x,Embed t'), t) <- unbind binding
  isValue t'

isValue (ELambda b) = return True

isValue (ERec b) = return True

isValue (ETCast t) = return True

isValue (EApp (ETermVar x) t') = do
  v1 <- isValue (ETermVar x)
  v2 <- isValue t'
  return (v1 && v2)
  
isValue _ = return False


type Trace = [ETerm]

--reduce :: Integer -> EExpr -> (Integer -> EExpr -> TCMonad EExpr) -> TCMonad EExpr

-- | instantiate variable from the definition context.
inst :: ETerm -> TCMonad ETerm

inst (ETermVar x) = do 
  env <- ask
  case M.lookup (ArgNameTerm (translate x)) (snd env) of
    Just a -> eraseArg a
    Nothing -> typeError $ disp ("undefined") <+> disp x

-- | one step reduction
rewrite :: ETerm -> TCMonad ETerm 

rewrite (ETermVar x) = do 
  v <-isValue (ETermVar x)
  if v then return (ETermVar x) else inst (ETermVar x)

-- | beta-v reduction
rewrite (EApp t1 t2) = do 
  case t1 of
    ELambda b -> do
            v <- isValue t2
            if v then do 
                   (n, t) <- unbind b
                   return (subst n t2 t) else do t2'<- rewrite t2
                                                 return (EApp (ELambda b) t2')
    ERec b -> do
            v <- isValue t2
            if v then do 
                   ((x, f),t) <- unbind b
                   return (subst f (ERec b) (subst x t2 t)) else do t2' <- rewrite t2
                                                                    return (EApp (ERec b) t2')
    t -> do t' <- rewrite t
            return (EApp t' t2)

rewrite (ELet b t) = do 
  v <- isValue t
  if v then do 
         (x,t') <- unbind b
         return (subst x t t')  else do t1 <- rewrite t
                                        return (ELet b t1)


rewrite (ETCast t) = do 
  v <- isValue t
  if v then return t else do t' <- rewrite t
                             return (ETCast t')

rewrite (ECase t b) = do 
  v <- isValue t
  if v then
      let a = flat t in
      case head a of 
        (ETermVar x) -> do 
                        case lookup (name2String x) b of
                          Just branch -> do
                            (ls, t1) <- unbind branch
                            let n = zip ls (tail a) 
                            return (substs n t1)
                          Nothing -> typeError $ disp ("Can't find data constructors from the branches")
        _ -> typeError $ disp ("not a correct form")  else do  t' <- rewrite t
                                                               return $ ECase t' b

rewrite t = return t

reduce :: ETerm -> Integer -> TCMonad [ETerm]
reduce t 0 = return [t]
reduce t i = do t' <- rewrite t
                if aeq t t' then return [t'] else 
                    do
                      cs <- reduce t' (i-1)
                      return (t':cs)


joinable :: ETerm -> Integer -> ETerm  -> Integer -> TCMonad Bool
joinable t1 i t2 j = do trace1 <- reduce t1 i
                        trace2 <- reduce t2 j
                        let r = intersectBy aeq trace1 trace2
                        if null r then return False else return True


flat (EApp t1 t2) = flat t1 ++ flat t2
flat t = [t] 