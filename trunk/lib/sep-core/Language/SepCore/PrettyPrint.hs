{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances, UndecidableInstances, PackageImports #-}
-- I use Garrin's file as a template.
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
instance Disp Proof where
  disp  = cleverDisp
instance Disp Predicate where
  disp  = cleverDisp
instance Disp LogicalKind where
  disp  = cleverDisp
instance Disp Stage where
  disp  = cleverDisp
instance Disp ArgClass where  
  disp  = cleverDisp
instance Disp Arg where
    disp  = cleverDisp
instance Disp ArgName where
    disp  = cleverDisp
instance Disp Declaration where
    disp  = cleverDisp
instance Disp Progdef where
    disp  = cleverDisp
instance Disp Progdecl where
    disp  = cleverDisp
instance Disp Logicdecl where
    disp  = cleverDisp
instance Disp Proofdef where
    disp  = cleverDisp
instance Disp Preddecl where
    disp  = cleverDisp
instance Disp Preddef where
    disp  = cleverDisp
instance Disp Tele where
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


instance Display Stage where
  display Plus = return $ text "+"
  display Minus = return $ text "-"

instance Display ArgClass where
    display (ArgClassTerm t) = display t
    display (ArgClassPredicate p) = display p
    display (ArgClassLogicalKind l) = display l

instance Display Arg where
    display (ArgTerm t) = display t
    display (ArgPredicate p) = display p
    display (ArgProof p) = display p
    precedence (ArgTerm t) = precedence t
    precedence (ArgProof t) = precedence t
    precedence (ArgPredicate t) = precedence t

    
instance Display ArgName where
    display (ArgNameTerm t) = display t
    display (ArgNamePredicate p) = display p
    display (ArgNameProof l) = display l


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



  -- display e = error $ "display: " ++ show e

  precedence (TermVar _) = 12
  precedence (Type _) = 12
  precedence (TermApplication _ _ _) = 10
  precedence (Abort _) = 5
  precedence (Pi _ _) = 4
  
  precedence _ = 0
  
instance Display Proof where
  display (ProofVar p) = display p

  display (ProofLambda binding) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        return $ text "\\" <+> (parens (dn <+> colon <+> dty)) <+> text "." <+> dran

  display (p@(ProofApplication p0 arg)) = do
    d0 <- dParen (precedence p - 1) p0
    d1 <- dParen (precedence p) arg
    return $ d0 <+> d1


  display (t@(Join t0 t1)) = do
    d0 <- termParen (precedence t) t0
    d1 <- termParen (precedence t) t1
    return $ text "join" <+> d0 <+> d1

  display (w@(Valax t)) = do
    d <- termParen (precedence w) t
    return $ text "valax" <+> d

  display (t@(Contra t0)) = do
    d0 <- termParen (precedence t) t0
    return $ text "contra" <+> d0


  precedence (ProofVar _) = 12
  precedence (ProofApplication _ _ ) = 10
  precedence (Join _ _ ) = 5
  precedence (Contra _ ) = 5
  precedence (Valax _ ) = 5
  
  precedence _ = 0

instance Display Predicate where
  display (PredicateVar p) = display p

  display (PredicateLambda binding) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        return $ text "\\" <+> (parens (dn <+> colon <+> dty)) <+> text "." <+> dran

  display (Forall binding) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        return $ text "Forall" <+> (parens (dn <+> colon <+> dty)) <+> text "." <+> dran

  display (p@(PredicateApplication p0 arg)) = do
    d0 <- dParen (precedence p - 1) p0
    d1 <- dParen (precedence p) arg
    return $ d0 <+> d1

  display (t@(Equal t0 t1)) = do
                     d0 <- dParen (precedence t) t0
                     d1 <- dParen (precedence t) t1
                     return $ fsep [d0, text "=", d1]

  display (w@(Terminate t)) = do
                     dt <- termParen (precedence w) t
                     return $ text "!" <+>  dt
  
  display (t@(Bottom i)) = return $ text "bottom" <+> integer i


  precedence (PredicateVar _) = 12
  precedence (PredicateApplication _ _ ) = 10
  precedence (Equal _ _ ) = 9
  precedence (Terminate _ ) = 7
  
  precedence _ = 0

instance Display LogicalKind where
  display (Formula i) = return $ text "formula" <+> integer i

  display (QuasiForall binding) = do
      lunbind binding fmt
    where fmt ((n,Embed ty),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        return $ text "Forall" <+> (parens (dn <+> colon <+> dty)) <+> text "." <+> dran

instance Display Declaration where
    display (DeclData d) = display d
    display (DeclPreddecl p) = display p
    display (DeclPreddef p) = display p
    display (DeclProgdef p) = display p
    display (DeclProgdecl p) = display p
    display (DeclProof p) = display p
    display (DeclLogic p) = display p

instance Display Progdef where
  display (Progdef n ty) = do
    dn <- display n
    dty <- display ty
    return $  dn <+> text "::" <+> dty <+> text "."

instance Display Progdecl where
  display (Progdecl n tm) = do
    dn <- display n
    dtm <- display tm
    return $  cat[ dn <+> text ":=", nest 3 $ dtm <> semi] $$ text ""

instance Display Logicdecl where
  display (Logicdecl n ty) = do
    dn <- display n
    dty <- display ty
    return $  dn <+> text "::" <+> dty <> semi
            
instance Display Proofdef where
  display (Proofdef n tm) = do
    dn <- display n
    dtm <- display tm
    return $  cat[ dn <+> text ":=", nest 3 $ dtm <> semi] $$ text ""

instance Display Preddecl where
  display (Preddecl n ty) = do
    dn <- display n
    dty <- display ty
    return $ dn <+> text "::" <+> dty <> semi
            
instance Display Preddef where
  display (Preddef n tm) = do
    dn <- display n
    dtm <- display tm
    return $  cat[ dn <+> text ":=", nest 3 $ dtm <> semi] $$ text ""


instance Display Datatypedecl where
  display (Datatypedecl t1 binding) = do
    lunbind binding $ \(tele,cs) -> do
     d1 <- display t1
     dtele <- displayTele tele
     dcs <- mapM displayCons cs
     return $ hang (text "data" <+> d1 <+> colon <>colon <+> dtele <+> text "where") 2
                       (vcat (punctuate semi dcs)) $$ text "."
    where displayCons (c,t) = do
            dc <- display c
            dt <- display t
            return $ dc <+> colon <+> dt

          displayTele Empty = return $ text "Type"
          displayTele tele = do
             dtele <- display tele
             return $ dtele <+> text ".Type"



instance Display Tele where
    display Empty = return empty
    display (TCons binding) = do
      let ((n,stage,Embed ty),tele) = unrebind binding
      dn <- display n
      dty <- display ty
      drest <- display tele
      dst <- display stage
      return $ text "Pi" <+> parens (dn <> colon <> dst <> dty) <> drest
        


