{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances, UndecidableInstances #-}
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
  precedence :: a -> Int
  precedence x = 0

dParen:: (Functor m,Fresh m,Disp a) => Int -> a -> m Doc
dParen level x =
   if level >= (precedence x)
      then do { d <- disp x; return(parens d)}
      else disp x

termParen:: (Functor m,Fresh m,Disp a) => Int -> a -> m Doc
termParen level x =
   if level <= (precedence x)
      then do { d <- disp x; return(parens d)}
      else disp x

-- Set the precedence to i. If this is < than the current precedence, then wrap
-- this with parens.
-- withPrec:: Int -> m
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

  disp (t@(App t0 stage t1)) = do
    d0 <- dParen (precedence t - 1) t0
    d1 <- dParen (precedence t) t1
    return $ d0 <+> ann stage d1
   where ann Static = brackets
         ann Dynamic = id


  disp (Lambda kind stage binding) = do
    ((n,ty),body) <- unbind binding
    dty <- disp ty
    dn <- disp n
    dbody <- disp body
    return $ text "\\" <+> bindingWrap stage (dn <+> colon <+> dty) <+>
             absOp kind <+> dbody

    where absOp Form = text "=>"
          absOp Program = text "->"

  disp (Case scrutinee termWitness binding) = do
    (consEq,alts) <- unbind binding
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


  disp (t@(Equal t0 t1)) = do
                     d0 <- dParen (precedence t) t0
                     d1 <- dParen (precedence t) t1
                     return $ d0 <+> text "=" <+> d1

  disp (w@(Val t)) = do
    d <- termParen (precedence w) t
    return $ text "value" <+> d

  disp (w@(Terminates t)) = do
                     dt <- termParen (precedence w) t
                     return $ dt <+> text "!"


  disp (t@(Contra t0)) = do
    d0 <- termParen (precedence t) t0
    return $ text "contra" <+> d0

  disp (t@(ContraAbort t0 t1)) = do
    d0 <- termParen (precedence t) t0
    d1 <- termParen (precedence t) t1
    return $ text "contraabort" <+> d0 <+> d1

  disp (w@(Abort t)) = do
    d <- dParen (precedence w) t
    return $ text "abort" <+> d

  disp (Conv t pfs binding) = do
    (vars,ty) <- unbind binding
    dVars <- mapM disp vars
    dTy <- disp ty
    dt <- disp t
    dPfs <- mapM disp pfs
    return $ sep ([text "conv" <+> dt, text "by"] ++
                  (punctuate comma dPfs) ++
                  [text "at"] ++
                  dVars ++
                  [text ".", dTy])

  -- Context-style conversions
  disp (ConvCtx t ctx) = do
    dt <- disp t
    dctx <- disp ctx
    return $ sep [text "conv" <+> nest 5 dt,text "at" <+> nest 3 dctx]


  disp (Escape t) = do
    dt <- disp t
    return $ text "~" <> dt


  disp (t@(Ord t0)) = do
    d0 <- termParen (precedence t) t0
    return $ text "ord" <+> d0

  disp (t@(OrdTrans t0 t1)) = do
    d0 <- termParen (precedence t) t0
    d1 <- termParen (precedence t) t1
    return $ text "ordtrans" <+> d0 <+> d1


  disp (t@(IndLT t0 t1)) = do
     d0 <- dParen (precedence t) t0
     d1 <- dParen (precedence t) t1
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
           brackets du <+> text ".",
           nest 2 dBody]


  disp (Rec binding) = do
    ((f,(x,ty)),body) <- unbind binding
    df <- disp f
    dx <- disp x
    dTy <- disp ty
    dBody <- disp body
    return $
      sep [text "rec" <+> df <+> parens (dx <+> colon <+> dTy) <+>
           text ".",
           nest 2 dBody]


  disp (t@(Let binding)) = do
    (ds,body) <- linearizeLet t
    let f (x,y,Embed z) =
         do dx <- disp x
            dy <- disp y
            dz <- disp z
            return(sep [dx <+> brackets dy <+> text "=",nest 3 dz])
    docs <- mapM f ds
    db <- disp body
    return $ sep
      [text "let" <+> nest 4 (sep (punctuate (text ";") docs)), text "in" <+> db]


  disp (t@(Aborts c)) = do
    dc <- dParen (precedence t) c
    return $ text "aborts" <+> dc
  disp (t@(Ann t0 t1)) = do
    d0 <- dParen (precedence t) t0
    d1 <- dParen (precedence t) t1
    return $ d0 <+> colon <+> d1


  disp (Pos _ t) = disp t
  disp (t@(Sym x)) = do
    dx <- dParen (precedence t) x
    return $ text "sym" <+> dx

  -- disp e = error $ "disp: " ++ show e

  precedence (Pos _ t) = precedence t
  precedence (Var _) = 12
  precedence (Con _) = 12
  precedence (Type) = 12
  precedence (Escape _) = 11
  precedence (App _ _ _) = 10
  precedence (Equal _ _) = 9
  precedence (IndLT _ _) = 8
  precedence (Terminates _) = 7
  precedence (Ann _ _) = 6

  precedence (Contra _) = 5
  precedence (Val _ ) = 5
  precedence (ContraAbort _ _) = 5
  precedence (Ord _) = 5
  precedence (OrdTrans _ _) = 5
  precedence (Aborts _) = 5
  precedence (Sym _) = 5

  precedence (Pi Dynamic _) = 4
  precedence (Pi Static _) = 4
  precedence _ = 0


linearizeLet (Pos _ t) = linearizeLet t
linearizeLet (Let binding) =
  do (triple,body) <- unbind binding
     (ds,b) <- linearizeLet body
     return(triple:ds,b)
linearizeLet x = return ([],x)

-- bindingWrap adds the correct stage annotation for an abstraction binding.
bindingWrap Dynamic = parens
bindingWrap Static = brackets

instance Disp Decl where
  disp (ProgDecl n ty val) = do
    dn <- disp n
    dty <- disp ty
    dval <- disp val
    return $ text "prog" <+> dn <+> text ":" <+> dty <> semi $$
             cat[text "def" <+> dn <+> text "=", nest 3 $ dval <> semi] $$ text ""


  disp (ProofDecl n ty val) = do
    dn <- disp n
    dty <- disp ty
    dval <- disp val
    return $ text "theorem" <+> dn <+> text ":" <+> dty <> semi $$
             cat[text "proof" <+> dn <+> text "=",nest 3 $ dval <> semi] $$ text ""


  disp (DataDecl t1 t2 cs) = do
     d1 <- disp t1
     d2 <- disp t2
     dcs <- mapM dispCons cs
     return $ hang (text "data" <+> d1 <+> colon <+> d2 <+> text "where") 2
                       (vcat (punctuate semi dcs)) $$ text ""
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



-- instance Show TypeError where
--     show e = render $ disp e



runDisp t = render $ runFreshM (disp t)

