{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances, UndecidableInstances, PackageImports #-}
module Language.SepCore.PrettyPrint where

import Language.SepCore.Syntax

import Unbound.LocallyNameless hiding (empty,Val,Con,Refl,Equal)

import Text.PrettyPrint
import Control.Applicative hiding (empty)
import "mtl" Control.Monad.Reader
import Text.Parsec.Pos
import Text.Parsec.Error(ParseError,showErrorMessages,errorPos,errorMessages)
import qualified Data.Set as S


import Debug.Trace

class Disp d where
  disp :: d -> Doc


instance Disp Doc where
  disp = id
instance Disp String where
  disp  = text
instance Disp Term where
  disp  = cleverDisp
-- instance Disp Proof where
--   disp = cleverDisp
instance Rep a => Disp (Name a) where
  disp = cleverDisp
instance Disp Int where
  disp = integer . toInteger

-- instance Disp Tele where
--   disp = cleverDisp

-- Adapted from an adaptation from AuxFuns.
data DispInfo = DI {
    dispAvoid :: S.Set AnyName
  }

initDI :: DispInfo
initDI = DI S.empty

-- We still wrap this in a Fresh monad, so that we can print all of the
-- variables with their indicies, for debugging purposes.
type M = FreshMT (Reader DispInfo)

-- If we set 'barenames' to true, then we don't try to do any clever name stuff with lfresh.
barenames = True
instance LFresh M where
  lfresh nm = do
    if barenames
       then fresh nm
        else do
          let s = name2String nm
          di <- ask
          return $ head (filter (\x -> AnyName x `S.notMember` (dispAvoid di))
                         (map (makeName s) [0..]))

  avoid names = local upd where
     upd di = di { dispAvoid = (S.fromList names) `S.union` (dispAvoid di) }

-- This function tries to pretty-print terms using the lowest number in
-- the names of the variable (i.e. as close to what the user originally
-- wrote.)
-- It first freshens the free variables of the argument (using the lowest
-- numbers that it can) then displays the term, swapping the free variables
-- with their new name in the process

cleverDisp :: (Display d, Alpha d) => d -> Doc
cleverDisp d =
  runReader (runFreshMT dm) initDI where
    dm = let vars = S.elems (fvAny d)  in
         lfreshen vars $ \vars'  p ->
           (display (swaps p d))

-- 1. Display is monadic :: a -> M Doc
-- 2. Disp is pure :: a -> Doc

-- display :: Disp a => a -> IO Doc
-- display d = runFreshMT $ runReaderT (disp d) 0


class (Alpha t) => Display t where
  display :: t -> M Doc
  precedence :: t -> Int
  precedence _ = 0

instance Display String where
  display = return . text
instance Display Int where
  display = return . text . show
instance Display Integer where
  display = return . text . show
instance Display Double where
  display = return . text . show
instance Display Float where
  display = return . text . show
instance Display Char where
  display = return . text . show
instance Display Bool where
  display = return . text . show


-- class Disp a where
 --   disp :: (Functor m, Fresh m) => a -> m Doc
--   precedence :: a -> Int
--   precedence x = 0

dParen:: (Display a) => Int -> a -> M Doc
dParen level x =
   if level >= (precedence x)
      then do { d <- display x; return(parens d)}
      else display x

termParen:: (Display a) => Int -> a -> M Doc
termParen level x =
   if level <= (precedence x)
      then do { d <- display x; return(parens d)}
      else display x

-- Set the precedence to i. If this is < than the current precedence, then wrap
-- this with parens.
-- withPrec:: Int -> m
withPrec i m = do
  dm <- local (const i) m
  cur <- ask
  if i < cur
     then return $ parens dm
     else return $ dm

instance Rep a => Display (Name a) where
  display = return . text . name2String


instance Display Stage
instance Display ArgClass
instance Display Arg
instance Display ArgName
instance Display Term where
  display (TermVar n) = return $ text $ name2String n
  
  display (Type i) = return $ text "Type" <+> integer i
  
  display (Pi binding stage) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        dstage <- display stage
                        return $ text "Pi" <+> (parens (dn <+> colon <+> dstage <+> dty)) <+> text "." <+> dran

  display (TermLambda binding stage) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        dstage <- display stage
                        return $ text "\\" <+> (parens (dn <+> colon <+> dstage <+> dty)) <+> text "." <+> dran

  display (t@(TermApplication t0 arg stage)) = do
    d0 <- dParen (precedence t - 1) t0
    d1 <- dParen (precedence t) arg
    return $ d0 <+> ann stage d1
   where ann Minus = brackets
         ann Plus = id

  display (TermCase1 scrutinee alts) = do
    dScrutinee <- display scrutinee
    dAlts <- mapM dAlt alts
    return $ text "case" <+> dScrutinee <+> text "of" $$
             nest 2 (vcat dAlts)
    where dAlt (con, binding) = do
            lunbind binding $ \(vars,body) -> do
            dcon <- display con
            dPvars <- mapM (\var -> display var) vars
            dBody <- display body
            return $ cat [dcon <+> hsep dPvars <+> text "-> ",nest 2 dBody]
              
  display (w@(Abort t)) = do
    d <- dParen (precedence w) t
    return $ text "abort" <+> d

  display (Rec binding) = do
    lunbind binding $ \((x,f,Embed ty),body) -> do
      df <- display f
      dty <- display ty
      dx <- display x
      dBody <- display body
      return $
         sep [text "rec" <+> dx <+> df <+> text ":" <+> parens dty,
              text ".",
              nest 2 dBody]

  display (t@(Abort c)) = do
    dc <- dParen (precedence t) c
    return $ text "abort" <+> dc


  -- display e = error $ "display: " ++ show e

  precedence (TermVar _) = 12
  precedence (Type _) = 12
  precedence (TermApplication _ _ _) = 10
  precedence (Abort _) = 5
  precedence (Pi _ _) = 4
  precedence _ = 0


{-
-- bindingWrap adds the correct stage annotation for an abstraction binding.
bindingWrap Dynamic = parens
bindingWrap Static = brackets

instance Display Decl where
  display (ProgDecl n ty val) = do
    dn <- display n
    dty <- display ty
    dval <- display val
    return $ text "type" <+> dn <+> text ":" <+> dty <> semi $$
             cat[text "prog" <+> dn <+> text "=", nest 3 $ dval <> semi] $$ text ""


  display (ProofDecl n ty val) = do
    dn <- display n
    dty <- display ty
    dval <- display val
    return $ text "theorem" <+> dn <+> text ":" <+> dty <> semi $$
             cat[text "proof" <+> dn <+> text "=",nest 3 $ dval <> semi] $$ text ""

  display (AxiomDecl n ty) = do
    dn <- display n
    dty <- display ty
    return $ text "axiom" <+> dn <+> text ":" <+> dty <> semi


  display (DataDecl t1 binding) = do
    lunbind binding $ \(tele,cs) -> do
     d1 <- display t1
     -- d2 <- display t2
     dtele <- displayTele tele
     dcs <- mapM displayCons cs
     return $ hang (text "data" <+> d1 <+> colon <+> dtele <+> text "where") 2
                       (vcat (punctuate semi dcs)) $$ text ""
    where displayCons (c,t) = do
            dc <- display c
            dt <- display t
            return $ dc <+> colon <+> dt


          displayTele Empty = return $ text "Type"
          displayTele tele = do
             dtele <- display tele
             return $ dtele <+> text "-> Type"




instance Display Module where
  display (Module n bindings) = do
    dn <- display n
    dbindings <- mapM display bindings
    return $ text "module" <+> dn <+> text "where" $$
             cat dbindings


instance Display a => Display (Embed a) where
  display (Embed e) = display e



instance Display EExpr where
  display (EVar v) = display v
  display (ECon c) = display c
  display EType = return $ text "Type"
  display t@(EApp t1 t2) = do
     d1 <- etermParen (precedence t - 1) t1
     d2 <- etermParen (precedence t) t2
     return $ d1 <+> d2
  display t@(ERec binding) = do
    lunbind binding $ \((f,args),body) -> do
    df <- display f
    dx <- mapM display args
    dbody <- etermParen (precedence t) body
    -- return $ text "rec" <+> df <+> (hcat dx) <+> text "." <+> dbody
    return df

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
   where displayAlt alt = do
           lunbind alt $ \((c,pvars),body) -> do
           dbody <- display body
           dpvars <- mapM display pvars
           return $ fsep $ [text c <+> hsep dpvars <+> text "->", nest 2 dbody]

  display t@(ELet binding) = do
     lunbind binding $ \((n,t),body) -> do
     dn <- display n
     dt <- display t
     dbody <- display body
     return $ text "let" <+> dn <+> text "=" <+> dt $$
              text "in" <+> dbody
  display t@(EPi stage binding) = do
     lunbind binding $ \((n,t),body) -> do
     dn <- display n
     dt <- display t
     dbody <- display body
     return $ bindingWrap stage (dn <+> colon <+> dt) <+> text "->" <+> dbody


  display (ETCast t) = do
     dt <- display t
     return $ text "tcast" <+> dt

  display EAbort = return $ text  "abort"



  precedence (EVar _) = 12
  precedence (ECon _) = 12
  precedence (EApp _ _) = 10
  precedence (ERec _) = 0
  precedence (ELambda _) = 0
  precedence (ECase _ _) = 1
  precedence (ETCast _) = 11
  precedence (EPi _ _) = 4
  precedence EAbort  = 0
  precedence tm = error $ "precedence is not defined for " ++ (show tm)



etermParen:: (Display a) => Int -> a -> M Doc
etermParen level x
  | level >= (precedence x) = parens <$> display x
  | otherwise =  display x


-- instance Show TypeError where
--     show e = render $ display e



-- runDisplay t = render $ runFreshM (display t)

instance Disp Stage where
  disp Static = text "static"
  disp Dynamic = text "runtime"

instance Disp SourcePos where
  disp sp =  text (sourceName sp) <> colon <> int (sourceLine sp) <> colon <> int (sourceColumn sp) <> colon

instance Disp ParseError where
 disp pe = do
    hang (disp (errorPos pe)) 2
             (text "Parse Error:" $$ sem)
  where sem = text $ showErrorMessages "or" "unknown parse error"
              "expecting" "unexpected" "end of input"
              (errorMessages pe)


instance Display Tele where
    display Empty = return empty
    display (TCons binding) = do
      let ((n,stage,Embed ty,inf),tele) = unrebind binding
      dn <- display n
      dty <- display ty
      drest <- display tele
      let dinf = if inf then text "?" else empty
      case stage of
        Static -> return $ brackets (dinf <+> dn <> colon <> dty) <> drest
        Dynamic -> return $ parens (dinf <+> dn <> colon <> dty) <> drest
-}
