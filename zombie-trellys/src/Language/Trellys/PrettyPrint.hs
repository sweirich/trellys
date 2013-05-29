{-# LANGUAGE TypeSynonymInstances,ExistentialQuantification,FlexibleInstances, UndecidableInstances,
             ViewPatterns
 #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing #-}

-- | A Pretty Printer for the core trellys. The 'Disp' class and
-- 'D' type should
-- be replace with their LangLib equivalents.
module Language.Trellys.PrettyPrint(Disp(..), D(..))  where

import Language.Trellys.Syntax
import Language.Trellys.GenericBind

import Control.Monad.Reader
import Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.ParserCombinators.Parsec.Error (ParseError)
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (intersperse)
import Control.Applicative ((<$>), (<*>))

-- | The 'Disp' class governs types which can be turned into 'Doc's
class Disp d where
  disp :: d -> Doc


-- This function tries to pretty-print terms using the lowest number in
-- the names of the variable (i.e. as close to what the user originally
-- wrote.)
-- It first freshens the free variables of the argument (using the lowest
-- numbers that it can) then displays the term, swapping the free variables
-- with their new name in the process
cleverDisp :: (Display d, Alpha d) => d -> Doc
cleverDisp d =
  runReader dm initDI where
    dm = let vars = S.elems (fvAny d)  in
         lfreshen vars $ \vars'  p ->
           (display (swaps p d))

instance Disp Term where
  disp = cleverDisp
instance Disp ETerm where
  disp = cleverDisp
instance Rep a => Disp (Name a) where
  disp = cleverDisp
instance Disp Telescope where
  disp = cleverDisp
instance Disp Pattern where 
  disp = cleverDisp
instance Disp ComplexMatch where
  disp = cleverDisp
instance Disp ATerm where
  disp = cleverDisp
instance Disp ATelescope where
  disp = cleverDisp
instance Disp AConstructorDef where
  disp = cleverDisp

-------------------------------------------------------------------------
-- Adapted From AuxFuns
-------------------------------------------------------------------------
-- | The data structure for information about the display
-- 
-- In a more perfect world this would also include the current precedence
-- level, so we could print parenthesis exactly when needed.
data DispInfo = DI
  {
  dispAvoid :: Set AnyName -- ^ names that have already been used
  }

-- | An empty 'DispInfo' context
initDI :: DispInfo
initDI = DI S.empty

instance LFresh (Reader DispInfo) where
  lfresh nm = do
      let s = name2String nm
      di <- ask;
      return $ head (filter (\x -> AnyName x `S.notMember` (dispAvoid di))
                      (map (makeName s) [0..]))
  avoid names = local upd where
     upd di = di { dispAvoid = (S.fromList names) `S.union` (dispAvoid di) }

  getAvoids = dispAvoid <$> ask

type M = Reader DispInfo

-- | The 'Display' class is like the 'Disp' class. It qualifies
--   types that can be turned into 'Doc'.  The difference is that the
--   type might need the 'DispInfo' context to turn a long
--   machine-generated name into a short user-readable one.
--
--   Minimal complete definition: 'display'.

class (Alpha t) => Display t where
  -- | Convert a value to a 'Doc'.
  display  :: t -> M Doc
  -- | Convert a value to a 'String'. Default definition: @'render' . 'cleverDisp'@.
  showd :: t -> String
  -- | Print a value to the screen.  Default definition: @'putStrLn' . 'showd'@.
  pp    :: t -> IO ()

  -- Default implementations that can be overridden
  showd = render . cleverDisp
  pp    = putStrLn . showd


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

-------------------------------------------------------------------------

bindParens :: Epsilon -> Doc -> Doc
bindParens Runtime d = d
bindParens Erased  d = brackets d

mandatoryBindParens :: Epsilon -> Doc -> Doc
mandatoryBindParens Runtime d = parens d
mandatoryBindParens Erased  d = brackets d

instance Disp Module where
  disp m = text "module" <+> disp (moduleName m) <+> text "where" $$
           vcat (map disp (moduleImports m)) $$
           vcat (map disp (moduleEntries m))

instance Disp Decl where
  disp (Def n r@(Ind _ bnd)) | name2String(fst(fst(unsafeUnbind bnd)))==name2String n = disp r
  disp (Def n r@(Rec _ bnd))    | name2String(fst(fst(unsafeUnbind bnd)))==name2String n = disp r
  disp (Def n term) = disp n <+> text "=" <+> disp term

  disp (Sig n th ty) =
        disp th <+> disp n <+> text ":" <+> disp ty
  disp (Axiom n th ty) =
        text "axiom"
    <+> disp th <+> disp n <+> text ":" <+> disp ty

  disp (Data n params lev constructors) =
    hang (text "data" <+> disp n <+> disp params
           <+> colon <+> text "Type" <+> text (show lev)
           <+> text "where")
           2 (vcat $ map disp constructors)
  disp (AbsData t delta lev) =
        text "data" <+> disp t <+> disp delta <+> colon
    <+> text "Type" <+> text (show lev)

instance Disp Goal where
  disp (Goal ctx statement) = 
   foldr ($+$) empty (map dispAssumption ctx)
   $+$ text "========================================="
   $+$ disp statement
{-
   $+$ text "\nOr printed less prettily:"
   $+$ foldr ($+$) empty (map (text . show) ctx)
   $+$ text "========================================="
   $+$ text (show statement)
-}
   where dispAssumption (a, aTy) = disp a <+> colon <+> disp aTy

instance Disp ConstructorDef where
  disp (ConstructorDef _ c tele) = disp c <+> text "of" <+> disp tele


instance Disp ModuleImport where
  disp (ModuleImport i) = text "import" <+> disp i

instance Display Term where
  display (Var n) = display n

  display (UniVar n) = return $ text ("?" ++ show n)

  display (isNumeral -> Just i) = display i

  display (TCon n args) = do
    dn <- display n
    dargs <- mapM displayArg args
    return $ dn <+> hsep dargs
      where displayArg (t, ep) = do dt <- display t
                                    return $ wraparg t $ bindParens ep dt

  display (DCon n args) = do
    dn <- display n
    dargs <- mapM displayArg args
    return $ dn <+> hsep dargs
      where displayArg (t, ep) = do dt <- display t
                                    return $ wraparg t $ bindParens ep dt


  display (Type n) = return $ text "Type" <+> (text $ show n)

  display (Arrow ex ep bnd) = do
     lunbind bnd $ \((n,a), b) -> do
        da <- display (unembed a)
        dn <- display n
        db <- display b
        return $ (mandatoryBindParens ep $ dn  <+> colon <+> da) 
                 <+> text (case ex of { Explicit -> "->" ; Inferred -> "=>" })
                 <+> db

  display (Lam ep b) =
    lunbind b $ \(n, body) -> do
      dn <- display n
      db <- display body
      return $ text "\\" <+> bindParens ep dn
               <+> text "." <+> db

  display (Ind ep binding) =
    lunbind binding $ \ ((n,x),body) -> do
      dn <- display n
      dx <- display x
      db <- display body
      return $ text "ind" <+> dn <+> bindParens ep dx <+> text "="
               <+> db

  display (Rec ep binding) =
    lunbind binding $ \ ((n,x),body) -> do
      dn <- display n
      dx <- display x
      db <- display body
      return $ parens $
             text "rec" <+> dn <+> bindParens ep (dx) <+> text "=" $$
                    (nest 2 db)

  display (App ep f x) = do
     df <- display f
     dx <- display x
     return $ wrapf f df <+> wraparg x (bindParens ep dx)
  display (Paren e) = do
     de <- display e
     return $ (parens de)

  display (Pos _ e) = display e

  display (Let th ep bnd) = do

    lunbind bnd $ \ ((x,y,a) , b) -> do
     da <- display (unembed a)
     dx <- display x
     dy <- display y
     db <- display b
     return $  sep [text "let" <+> tag <+> bindParens ep dx
                    <+> brackets dy <+> text "=" <+> da
                    <+> text "in",
                    db]
     where
       tag = case th of {Logic -> empty; Program -> text "prog"}

  display (ComplexCase bnd) =
    lunbind bnd $ \ (scruts,  alts) -> do
     let displayScrutinee (s,y) = do
           ds <- display (unembed s)
           dy <- display y
           return $ ds <+> brackets dy
     dscruts <-  (hsep . intersperse (text ",")) <$> mapM displayScrutinee scruts
     dalts <- mapM display alts
     return $ text "case" <+> dscruts <+> text "of" $$
          (nest 2 $ vcat $  dalts)              
         
  display (Conv a bs bnd) =
    lunbind bnd $ \(xs,c) -> do
      da <- display a
      dbs <- mapM display bs
      dxs <- mapM display xs
      dc <- display c
      return $ fsep [text "conv" <+> da,
                    text "by" <+> sep (punctuate comma dbs),
                    text "at" <+> hsep dxs  <+> text "." <+> dc]

  display (Smaller a b) = do
      da <- display a
      db <- display b
      return $ da <+> text "<" <+> db

  display (OrdAx a) = do
      da <- display a
      return $ text "ord" <+> da

  display (OrdTrans a b) = do
      da <- display a
      db <- display b
      return $ text "ordtrans" <+> da <+> db

  display (TyEq a b)   = do
      da <- display a
      db <- display b
      return $ wraparg a da <+> text "=" <+> wraparg b db
  display (Join s1 s2) =
    return $ text "join" <+> text (if s1 == s2
                            then if s1 == 100
                                   then ""
                                   else show s1
                            else show s1 ++ " " ++ show s2)
  display (Unfold s a b) = do
    da <- display a
    db <- display b
    return $ text "unfold" <+> text (show s) <+> da <+> text "in"
              $$ nest 2 db
  display (Contra ty)  = do
     dty <- display ty
     return $ text "contra" <+> dty
  display (InjDCon t i) = do
     dt <- display t
     return $ text "injectivity" <+> dt <+> text (show i)
  display  Abort       = return $ text "abort"
  display (Ann a b)    = do
    da <- display a
    db <- display b
    return $ parens (da <+> text ":" <+> db)

  display (At ty th) = do 
    da <- display ty
    return $ da <+> text "@" <+> disp th

  display (TerminationCase scrutinee binding) =
    lunbind binding $ \(n,(diverge,tbind)) -> do
      lunbind tbind $ \(v, terminate) -> do 
          dScrutinee <- display scrutinee
          dDiverge <- display diverge
          dTerminate <- display terminate
          dn <- display n
          dv <- display v
          return $ hang (text "termcase" <+> dScrutinee <+> braces dn <+> text "of") 2
                        (braces (text "abort" <+> text "->" <+> dDiverge <> semi $$
                                 text "!" <+> dv <+> text "->" <+> dTerminate))

  display TrustMe = return $ text "TRUSTME"
  display InferMe = return $ text "_"

  display (SubstitutedFor  a x) = display a 
  display (SubstitutedForA a x) = display a                                

instance Display Match where
  display (Match c bd) =
    lunbind bd $ \ (vs, ubd) -> do
      dc <- display c
      dvs <- mapM display vs
      dubd <- display ubd
      return $ (hsep (dc : dvs)) <+> text "->" <+> dubd

instance Display ComplexMatch where
  display (ComplexMatch bnd) =
    lunbind bnd $ \ (pats, body) -> do
      dpats <- mapM display pats
      dbody <- display body
      return $ (hsep $ intersperse (text ",") dpats) <+> text "->" <+> dbody

instance Display Pattern where
  display (PatCon ec args) = 
    let c = unembed ec in
      parens <$> ((<+>) <$> (display c) <*> (hsep <$> (mapM display args)))
  display (PatVar x) = display x

wraparg :: Term -> (Doc -> Doc)
wraparg x = case x of
              Var _     -> id
              TCon _ [] -> id
              DCon _ [] -> id
              TrustMe   -> id
              _         -> parens
wrapf :: Term -> (Doc -> Doc)
wrapf f = case f of
            Var _       -> id
            App _ _ _   -> id
            _           -> parens

aWrapf :: ATerm -> Doc -> Doc
aWrapf a =  case a of
              AVar _       -> id
              AApp _ _ _ _ -> id
              _            -> parens

aWraparg :: Epsilon -> ATerm -> Doc -> Doc
aWraparg ep b = case b of
                 AVar _        -> bindParens ep
                 ATCon _ []    -> bindParens ep 
                 ADCon _ [] [] -> bindParens ep
                 _             -> mandatoryBindParens ep

{-
epParens :: Epsilon -> [DispElem] -> DispElem
epParens Runtime l = Dd (brackets (displays l))
epParens Erased  l = Dd displays l
-}

instance Display ATerm where
  display (AVar v) = display v
  display (AUniVar v a) = do
    da <- display a
    return $ text ("?" ++ show v) <+> colon <+> da
  display (ACumul a level) = display a
  display (AType level) = return $ text "Type" <+> int level
  display (AUnboxVal a) = do
    da <- display a
    return $ text "unbox" <+> aWraparg Runtime a da
  display (ATCon n params) = do
    dn <- display n
    dparams <- mapM (\a -> aWraparg Runtime a <$> display a) params
    return $ dn <+> hsep dparams
  display (ADCon n params args) = do
    dn <- display n
    dparams <- mapM (\a -> aWraparg Runtime a <$> (brackets <$> (display a))) params
    dargs <-   mapM (\(a,ep) -> aWraparg ep a <$> (bindParens ep <$> (display a))) args
    return $ dn <+> hsep dparams <+> hsep dargs
  display (AArrow ex ep bnd) = 
    lunbind bnd $ \((n, unembed -> a), b) -> do 
      dn <- display n
      da <- display a
      db <- display b
      return $ (mandatoryBindParens ep $ dn <+> text ":" <+> da)
                 <+> text (case ex of { Explicit ->  "->" ; Inferred -> "=>" })
                 <+> db
  display (ALam ty ep bnd) = 
    lunbind bnd $ \(n, body) -> do
      dty <- display ty     
      dn <- display n
      dbody <- display body
      return $ text "\\" <+> dn <+> colon <+> dty <+> text "." <+> dbody
  display (AApp ep a b ty) = do 
    da <- display a 
    db <- display b
    return $ aWrapf a da <+> aWraparg ep b db
  display (AAt a th) = do
    da <- display a
    return $ da <+> text "@" <+> disp th
  display (ABox a th) = do
    da <- display a
    return $ text "box" <+> aWraparg Runtime a da
  display (AAbort a) = do
    da <- display a 
    return $ text "abort" <+> da
  display (ATyEq a b) = do
    da <- display a
    db <- display b
    return $ parens da <+> text "=" <+> parens db
  display (AJoin a i b j) = do
    da <- display a
    db <- display b
    return $ text "join" <+> parens da <+> disp i
                         <+> parens db <+> disp j
  display (AConv a pfs bnd ty) = 
    lunbind bnd $ \(xs, template) -> do 
      da <- display a
      dpfs <- mapM display pfs
      dxs <- mapM display xs
      dtemplate <- display template
      dty <- display ty
      return $ text "conv" <+> da
                $$ nest 2 (text "by" <+> hsep dpfs)
                $$ nest 2 (text "at" <+> hsep dxs <+> text "." <+> dtemplate)
                $$ nest 2 (colon <+> dty)
  display (AContra a aTy) = do
    da <- display a
    daTy <- display aTy
    return $ text "contra" <+> da <+> text ":" <+> daTy
  display (AInjDCon a i) = do
    da <- display a 
    return $ text "injectivity" <+> da <+> text (show i)
  display (ASmaller a b) = do
    da <- display a
    db <- display b
    return $ parens da <+> text "<" <+> parens db
  display (AOrdAx pf a) = do
    dpf <- display pf
    da <- display a
    return $ text "ordax :" <+> dpf <+> da <+> text "< ?"
  display (AOrdTrans a b) = do
    da <- display a
    db <- display b
    return $ text "ordtrans" <+> parens da <+> parens db
  display (AInd ty ep bnd) = 
    lunbind bnd $ \((n,m), body) -> do
      dty <- display ty
      dn <- display n
      dm <- display m
      dbody <- display body
      return $ parens (text "ind" <+> dn <+> bindParens ep dm 
                         <+> text ":" <+> dty
                         <+> text "."
                        $$ nest 2 dbody)
  display (ARec ty ep bnd) = 
    lunbind bnd $ \((n,m), body) -> do
      dty <- display ty
      dn <- display n
      dm <- display m
      dbody <- display body
      return $ parens (text "rec" <+> dn <+> bindParens ep dm 
                         <+> text ":" <+> dty
                         <+> text "."
                        $$ nest 2 dbody)
  display (ALet  ep bnd) = 
    lunbind bnd $ \((n,m, unembed -> a), b) -> do 
      dn <- display n
      dm <- display m
      da <- display a
      db <- display b
      return $ text "let" <+> dn <+> brackets dm <+> text "="
                     <+> da <+> text "in"
                $$ nest 2 db
  display (ACase a bnd ty) =
    lunbind bnd $ \(n,mtchs) -> do
      da <- display a
      dn <- display n
      dmtchs <- mapM display mtchs
      dty <- display ty
      return $ (parens (text "case" <+> da <+> brackets dn <+> text "of" $$
                         nest 2 (vcat dmtchs))
                 <+> text ":" <+> dty)
  display (ADomEq a) = do
    da <- display a 
    return $ text "domeq" <+> aWraparg Erased a da
  display (ARanEq a b) = do
    da <- display a 
    db <- display b
    return $ text "raneq" <+> aWraparg Erased a da <+> aWraparg Erased b db
  display (AAtEq a) = do
    da <- display a 
    return $ text "ateq" <+> aWraparg Erased a da
  display (ANthEq i a) = do
    da <- display a
    return $ text "ntheq" <+> int i <+> aWraparg Erased a da
  display (ATrustMe a) = do
    da <- display a
    return $ parens (text "TRUSTME" <+> colon <+> da)
  display (ASubstitutedFor a x) = display a

instance Display AMatch where
  display (AMatch c bnd) = 
    lunbind bnd $ \(args, body) -> do
      dc <- display c
      dargs <- display args
      dbody <- display body
      return $ dc <+> dargs <+> text "->" <+> dbody

instance Disp ADecl where
  disp (ASig x th ty) = 
    disp th <+> disp x <+> text ":" <+> disp ty
  disp (ADef x a) = do
    disp x <+> text "=" <+> disp a
  disp (AData n params level constructors) = 
    hang (text "data" <+> disp n <+> disp params
           <+> colon <+> text "Type" <+> int level
           <+> text "where")
         2
         (vcat $ map disp constructors)
  disp (AAbsData n params level) =
    text "data" <+> disp params 
       <+> colon <+> text "Type" <+> int level

instance Display AConstructorDef where
  display (AConstructorDef c tele) = do
                                       dtele <- display tele
                                       dc <- display c
                                       return $ dc <+> dtele
instance Display ATelescope where
  display AEmpty = return empty
  display (ACons bnd) = do
    let ((n, unembed->ty, ep), tele) = unrebind bnd
    dn <- display n
    dty <- display ty
    dtele <- display tele
    return $ mandatoryBindParens ep (dn <+> colon <+> dty) <+> dtele

instance Disp [ADecl] where
  disp = vcat . map disp

instance Disp AModule where
  disp m = text "module" <+> disp (aModuleName m) <+> text "where"
             $$ (vcat $ punctuate (text "\n") (map disp (aModuleEntries m)))

instance Display ETerm where
  display (EVar v) = display v
  display (EUniVar n) = return $ text ("?" ++ show n)
  display (ETCon n args) = do
    dn <- display n
    dargs <- mapM display args
    return $ dn <+> hsep dargs
  display (EDCon n args) = do
    dn <- display n
    dargs <- mapM display args
    return $ dn <+> hsep dargs
  display (EType level) = return $ text "Type" <+> int level
  display (EArrow ep a bnd) = do
     da <- display a
     lunbind bnd $ \ (n,b) -> do
        dn <- display n
        db <- display b
        return $ (mandatoryBindParens ep $ dn <+> text ":" <+> da)
                    <+> text "->" <+> db
  display (ELam  b) =
     lunbind b $ \ (n, body) -> do
       dn <- display n
       dbody <- display body
       return ( text "\\" <+> dn <+> text "." <+> dbody )
  display (EILam  body) = do
    dbody <- display body
    return ( text "\\ []." <+> dbody )
  display (EApp f x) = do
       df <- display f
       dx <- display x
       let wrapf = case f of
                     EVar _     -> id
                     EApp _ _   -> id
                     EIApp _    -> id
                     _          -> parens
       let wrapx = case x of
                     EVar _     -> id
                     ETCon _ [] -> id
                     EDCon _ [] -> id
                     _          -> parens
       return (wrapf df <+> wrapx dx)
  display (EIApp f) = do
       df <- display f
       let wrapf = case f of
                     EVar _     -> id
                     EApp _ _   -> id
                     _          -> parens
       return (wrapf df <+> text "[]")
  display (EOrdAx) = return $ text "ord"
  display (ESmaller e0 e1) = do
       de0 <- display e0
       de1 <- display e1
       return (de0 <+> text "<" <+> de1)
  display (ETyEq e0 e1) = do
       de0 <- display e0
       de1 <- display e1
       return (de0 <+> text "=" <+> de1)
  display EJoin = return $ text "join"
  display EAbort = return $ text "abort"
  display (ERecPlus bnd) =
     lunbind bnd $ \ ((n,w),body) -> do
        dn <- display n
        dw <- display w
        db <- display body
        return $ parens ( text "rec" <+> dn <+> brackets (dw)
                          <+> text "."
                          <+> db )
  display (EIndPlus bnd) =
     lunbind bnd $ \ ((n,w),body) -> do
        dn <- display n
        dw <- display w
        db <- display body
        return $ parens ( text "ind" <+> dn <+> brackets (dw)
                          <+> text "."
                          <+> db )
  display (ERecMinus bnd) =
     lunbind bnd $ \ (n,body) -> do
        dn <- display n
        db <- display body
        return $ parens ( text "rec" <+> dn
                          <+> text "."
                          <+> db )
  display (EIndMinus bnd) =
     lunbind bnd $ \ (n,body) -> do
        dn <- display n
        db <- display body
        return $ parens ( text "ind" <+> dn
                          <+> text "."
                          <+> db )
  display (ECase dis matches) = do
    ddis <- display dis
    dmatches <- mapM display matches
    return
      (text "case" <+> ddis <+> text "of" $$
        nest 2 (vcat dmatches))
  display (ELet val bnd) = do
    dval <- display val
    lunbind bnd $ \(n,body) -> do
      dn <- display n
      dbody <- display body
      return $ sep [text "let" <+> dn <+> text "="
                    <+> dval <+> text "in",
                    dbody]
  display EContra = return $ text "contra"
  display (EAt ty th) = do 
      dty <- display ty
      return $ dty <+> text "@" <+> disp th

  display ETrustMe = return $ text "TRUSTME"

instance Display EMatch where
  display (EMatch n bnd) = do
    dn <- display n
    lunbind bnd $ \(vars,body) -> do
       db <- display body
       dvs <- mapM display vars
       let pat = hcat $ punctuate space $ dvs
       return $ dn <+> pat <+> text "->" <+> db


instance Disp Epsilon where
  disp Erased = text "-"
  disp Runtime = text "+"

instance Display a => Display (a, Epsilon) where
  display (t, ep) = bindParens ep <$> display t

instance Display Telescope where 
  display ts = do
    dts <- mapM dentry ts
    return $ hcat dts where
          prns Runtime = parens
          prns Erased = brackets
          dentry (n, ty, ep) = do
            dn <- display n
            dty <- display ty
            return (prns ep $ dn <+> colon <+> dty)

instance Disp Theta where
  disp Logic = text "log"
  disp Program = text "prog"

-- Assumes that all terms were opened safely earlier.
instance Rep a => Display (Name a) where
  display n = if (name2String n == "_")
               then return $ text "_"
               else return $ (text . show) n

instance Disp SourcePos where
  disp p = text (sourceName p) <> colon <> int (sourceLine p) <>
                colon <> int (sourceColumn p) <> colon

-- | Error message quoting
data D = DS String -- ^ String literal
       | forall a . Disp a => DD a -- ^ Displayable value

instance Disp D where
  disp (DS s) = text s
  disp (DD d) = nest 2 $ disp d -- might be a hack to do the nesting here???

instance Disp Int where
  disp i = text $ show i

instance Disp [D] where
  disp dl = sep $ map disp dl

instance Disp [Term] where
  disp = vcat . map disp

instance Disp [Name ETerm] where
  disp = sep . punctuate comma . map disp

instance Disp [(Name Term,Term)] where
  disp = vcat . map disp

instance Disp (Name Term,Term) where
  disp (n,t) = parens $ (disp n) <> comma <+> disp t

instance Disp a => Disp (Maybe a) where
  disp (Just a) = text "Just" <+> disp a
  disp Nothing = text "Nothing"

instance (Disp a, Disp b) => Disp (Either a b) where
  disp (Left a) = text "Left" <+> disp a
  disp (Right a) = text "Right" <+> disp a

instance Disp ParseError where
  disp = text . show