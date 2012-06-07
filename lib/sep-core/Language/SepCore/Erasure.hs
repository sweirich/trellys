{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeSynonymInstances  #-}

module Language.SepCore.Erasure where 
import Language.SepCore.Syntax
import Language.SepCore.Error
import Language.SepCore.Lexer
import Language.SepCore.Typecheck2(ensureArgClassTerm)
import Language.SepCore.PrettyPrint
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Alpha(aeqR1)
import Unbound.LocallyNameless.Subst(substR1)

import Control.Monad.Error hiding (join)

import Control.Exception(Exception)
import Control.Applicative hiding (empty)

import Text.PrettyPrint


data ETerm =  ETermVar (Name ETerm)

           | EType Integer

           | EPi (Bind ((Name ETerm), Embed ETerm) ETerm) Stage

           | ELambda (Bind (Name ETerm) ETerm)
                                 
           | ELet (Bind (Name ETerm) ETerm) ETerm

           | ECase ETerm ETermBranches

           | ETCast ETerm  

           | EApp ETerm ETerm

           | EAbort

           | ERec (Bind (Name ETerm, Name ETerm) ETerm)
           
  deriving(Show)

type EScheme = [(Name ETerm)]

type ETermBranches = [(String,(Bind EScheme ETerm))]

$(derive [''ETerm])

instance Alpha ETerm where
  aeq' c (ETCast t1) t2 = t1 `aeq` t2
  aeq' c t1 (ETCast t2) = t1 `aeq` t2
  aeq' c t1 t2 = aeqR1 rep1 c t1 t2

instance Subst ETerm ETerm where
  isvar (ETermVar x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst ETerm Stage where
  isvar _ = Nothing

erase :: (Applicative m, Fresh m, MonadError TypeError m) => Term -> m ETerm

erase (Pos _ t) = erase t

erase (Type i) = return $ EType i

erase (TermVar n) = return $ ETermVar (translate n)

erase (TermApplication f _ Minus) = erase f

erase (TermApplication f (ArgTerm t) Plus) = EApp <$> (erase f) <*> (erase t)

erase (TermApplication f u Plus) = typeError $ disp("stage of the argument ")<+> disp u<+>disp("doesn't match the stage of function: ")<+>disp f

erase (TermLambda binding Minus) = do
  (_,body) <- unbind binding
  erase body

erase (TermLambda binding Plus) = do
  ((n,_),body) <- unbind binding
  t <- ensureArgNameTerm n
  ELambda <$> ((bind (translate t)) <$> erase body)
  

erase (Pi binding Plus) = do
  ((n,Embed tp),body) <- unbind binding
  n' <- ensureArgNameTerm n
  t <- ensureArgClassTerm tp
  et <- erase t
  eb <- erase body
  return $  EPi (bind ((translate n'),Embed et) eb ) Plus

erase (Pi binding Minus) = do
  ((n,Embed tp),body) <- unbind binding
  erase body

erase (Rec binding) = do
  ((n,f,_),body) <- unbind binding
  ERec <$> (bind (translate n, translate f)) <$> erase body

erase (TermLetTerm1 binding term) = do
  (x,body) <- unbind binding
  eb<- erase body
  et <- erase term
  return $ ELet (bind (translate x) eb) et

erase (TermLetProof binding proof) = do
  (x,body) <- unbind binding
  erase body

erase (TermCase1 scrutinee alts) = do
  ECase <$> erase scrutinee <*> mapM eraseAlt alts



erase (Tcast t p) = ETCast <$> erase t
erase (Abort _) = return EAbort

eraseAlt (str,binding) = do
  (vs,body) <- unbind binding
  let vs' = [translate v | (ArgNameTerm v) <- vs]
  eb <- erase body
  return (str,(bind vs' eb))

ensureArgNameTerm (ArgNameTerm t) = return t
ensureArgNameTerm _ = typeError $ disp ("expected a ArgNameTerm")
