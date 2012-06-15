{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeSynonymInstances  #-}

module Language.SepCore.Erasure where 
import Language.SepCore.Syntax
import Language.SepCore.Error
import Language.SepCore.Monad
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

etermParen:: (Display a) => Int -> a -> M Doc
etermParen level x
  | level >= (precedence x) = parens <$> display x
  | otherwise =  display x

instance Disp ETerm where
    disp = cleverDisp

instance Display ETerm where
  display (ETermVar v) = display v

  display (EType i) = return $ text "Type"<+> integer i

  display t@(EApp t1 t2) = do
     d1 <- etermParen (precedence t - 1) t1
     d2 <- etermParen (precedence t) t2
     return $ d1 <+> d2

  display t@(ERec binding) = do
    lunbind binding $ \((f,arg),body) -> do
    df <- display f
    dx <- display arg
    dbody <- etermParen (precedence t) body
    return $ text "rec" <+> dx <+>  df <+> text "." <+> dbody

  display t@(ELambda binding) =  do
    lunbind binding $ \(x,body) -> do
    dx <- display x
    dbody <- etermParen (precedence t) body
    return $ fsep [text "\\" <+> dx <+> text ".",nest 2 dbody]

  display t@(ECase s alts) = do
    ds <- display s
    alts <- mapM displayAlt alts
    return $ text "case" <+> ds <+> text "of" $$
             nest 2 (vcat alts)
   where displayAlt (con, binding) = do
           lunbind binding $ \(pvars,body) -> do
           dbody <- display body
           dpvars <- mapM display pvars
           return $ fsep $ [text con <+> hsep dpvars <+> text "->", nest 2 dbody]

  display (ELet binding t) = do
     lunbind binding $ \(n,body) -> do
     dn <- display n
     dt <- display t
     dbody <- display body
     return $ text "let" <+> dn <+> text "=" <+> dt $$
              text "in" <+> dbody

  display t@(EPi binding stage) = do
     lunbind binding $ \((n,Embed t),body) -> do
     dn <- display n
     dt <- display t
     dbody <- display body
     dst <- display stage
     return $ text "Pi"<+> (dn <+> colon<+>dst<+> dt) <+> text "." <+> dbody


  display (ETCast t) = do
     dt <- display t
     return $ text "tcast" <+> dt

  display EAbort = return $ text  "abort"



  precedence (ETermVar _) = 12

  precedence (EApp _ _) = 10
  precedence (ERec _) = 0
  precedence (ELambda _) = 0
  precedence (ECase _ _) = 1
  precedence (ETCast _) = 11
  precedence (EPi _ _) = 4
  precedence EAbort  = 0
  precedence tm = error $ "precedence is not defined for " ++ (show tm)

eraseArg (ArgTerm t) = erase t

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
  let vs' = [translate v | (ArgNameTerm v, Plus) <- vs]
  eb <- erase body
  return (str,(bind vs' eb))

ensureArgNameTerm (ArgNameTerm t) = return t
ensureArgNameTerm _ = typeError $ disp ("expected a ArgNameTerm")
