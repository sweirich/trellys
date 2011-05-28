{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable #-}
module Language.SepPP.PrettyPrint where

import Language.SepPP.Syntax

import Unbound.LocallyNameless hiding (empty,Val,Con)

import Text.PrettyPrint
import Control.Applicative hiding (empty)
import Control.Monad.Reader


display :: Disp a => a -> IO Doc
display d = runFreshMT $ runReaderT (disp d) 0


class Disp a where
  disp :: (Functor m, Fresh m) => a -> m Doc

-- Set the precedence to i. If this is < than the current precedence, then wrap
-- this with parens.
withPrec i m = do
  dm <- local (const i) m
  cur <- ask
  if i < cur
     then return $ parens dm
     else return $ dm

instance Disp (Name a) where
  disp = return . text . show

instance Disp Term where
  disp (Var n) = return $ text $ show n
  disp (Con n) = return $ text $ show n
  disp (Formula 0) = return $ text "Form"
  disp (Formula n) = return $ text "Form" <+> integer n
  disp Type = return $ text "Type"

  disp (Pi stage binding) = do
      ((n,ty),ran) <- unbind binding
      dn <- disp n
      dty <- disp ty
      dran <- disp ran
      return $ bindingWrap stage (dn <+> colon <+> dty) <+> text "->" <+> dran
    where wrap Dynamic = parens
          wrap Static =  brackets


  disp (Forall binding) = do
    ((n,ty),ran) <- unbind binding
    dn <- disp n
    dty <- disp ty
    dran <- disp ran
    return $ text "forall" <+> parens (dn <+> colon <+> dty) <+> text "." <+> dran

  disp (App t0 stage t1) = do
    d0 <- disp t0
    d1 <- disp t1
    return $ d0 <+> ann stage d1
   where ann Static = brackets
         ann Dynamic = id


  disp (Lambda kind stage binding) = do
    ((n,ty),body) <- unbind binding
    dty <- disp ty
    dn <- disp n
    dbody <- disp body
    return $ text "\\" <> bindingWrap stage (dn <+> colon <+> dty) <+>
             absOp kind <+> dbody

    where absOp Form = text "=>"
          absOp Program = text "->"

  disp (Case scrutinee consEq termWitness alts) = do
    dScrutinee <- disp scrutinee
    dConsEq <- braces <$> disp consEq
    dTermWitness <- maybe (return empty) (\v -> brackets <$> disp v) termWitness
    dAlts <- mapM dAlt alts
    return $ text "case" <+> dScrutinee <+> dConsEq <+> dTermWitness <+> text "of" $$
             nest 2 (braces $ vcat $ punctuate semi dAlts)

    where dAlt alt = do
            ((con,pvars),body) <- unbind alt
            dPvars <- mapM disp pvars
            dBody <- disp body
            return $ cat [text con <+> hsep dPvars <+> text "-> ",
                          nest 2 dBody]


  disp (TerminationCase scrutinee binding) = do
    dScrutinee <- disp scrutinee
    (n,(diverge,terminate)) <- unbind binding
    dDiverge <- disp diverge
    dTerminate <- disp terminate
    dn <- disp n
    return $ hang (text "termcase" <+> dScrutinee <+> braces dn <+> text "of") 2
               (braces (text "abort" <+> text "->" <+> dDiverge <> semi $$
                       text "!" <+> text "->" <+> dTerminate))


  disp (Join i0 i1) =
    return $ text "join" <+> integer i0 <+> integer i1


  disp (Equal t0 t1) = do
                     d0 <- disp t0
                     d1 <- disp t1
                     return $ d0 <+> text "=" <+> d1

  disp (Val t) = do
    d <- disp t
    return $ text "val" <+> d

  disp (Terminates t) = do
                     dt <- disp t
                     return $ dt <+> text "!"


  disp (Contra t0) = do
    d0 <- disp t0
    return $ text "contra" <+> d0

  disp (ContraAbort t0 t1) = do
    d0 <- disp t0
    d1 <- disp t1
    return $ text "contraabort" <+> d0 <+> text "using" <+> d1


  disp (Abort t) = do
    d <- disp t
    return $ text "abort" <+> d


  disp (Conv t pfs binding) = do
    (vars,ty) <- unbind binding
    dVars <- mapM disp vars
    dTy <- disp ty
    dt <- disp t
    dPfs <- mapM (\(erased,t) -> ann erased <$> disp t) pfs
    return $ sep ([text "conv", dt, text "by"] ++
                  (punctuate comma dPfs) ++
                  [text "at"] ++
                  dVars ++
                  [text ".", dTy])


   where ann True = brackets
         ann False = id


  disp (Ord t0 t1) = do
    d0 <- disp t0
    d1 <- disp t1
    return $ text "ord" <+> d0 <+> d1

  disp (IndLT t0 t1) = do
     d0 <- disp t0
     d1 <- disp t1
     return (d0 <+> text "<" <+> d1)



  disp (Ind binding) = do
    ((f,(x,ty),u),body) <- unbind binding
    df <- disp f
    dx <- disp x
    dTy <- disp ty
    dBody <- disp body
    du <- disp u
    return $
      sep [text "ind" <+> df <+> parens (dx <+> colon <+> dTy) <+>
           brackets du <+> text "->",
           nest 2 dBody]


  disp (Rec binding) = do
    ((f,(x,ty)),body) <- unbind binding
    df <- disp f
    dx <- disp x
    dTy <- disp ty
    dBody <- disp body
    return $
      sep [text "rec" <+> df <+> parens (dx <+> colon <+> dTy) <+>
           text "->",
           nest 2 dBody]


  disp (Ann t0 t1) = do
    d0 <- disp t0
    d1 <- disp t1
    return $ d0 <+> colon <+> d1


  disp (Parens p) = parens <$> disp p

  disp e = error $ "disp: " ++ show e

-- bindingWrap adds the correct stage annotation for an abstraction binding.
bindingWrap Dynamic = parens
bindingWrap Static = brackets

instance Disp Decl where
  disp (ProgDecl n ty val) = do
    dn <- disp n
    dty <- disp ty
    dval <- disp val
    return $ text "prog" <+> dn <+> text ":" <+> dty <> semi $$
             text "def" <+> dn <+> text "=" <+> dval <> semi


  disp (ProofDecl n ty val) = do
    dn <- disp n
    dty <- disp ty
    dval <- disp val
    return $ text "theorem" <+> dn <+> text ":" <+> dty <> semi $$
             text "proof" <+> dn <+> text "=" <+> dval <> semi


  disp (DataDecl t1 t2 cs) = do
     d1 <- disp t1
     d2 <- disp t2
     dcs <- mapM dispCons cs
     return $ hang (text "data" <+> d1 <+> colon <+> d2 <+> text "where") 2
                       (vcat (punctuate semi dcs))
    where dispCons (c,t) = do
            dc <- disp c
            dt <- disp t
            return $ dc <+> colon <+> dt

instance Disp Module where
  disp (Module n bindings) = do
    dn <- disp n
    dbindings <- mapM disp bindings
    return $ text "module" <+> dn <+> text "where" $$
             cat dbindings


instance Disp a => Disp (Embed a) where
  disp (Embed e) = disp e
