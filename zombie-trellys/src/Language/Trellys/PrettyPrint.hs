{-# LANGUAGE TypeSynonymInstances,ExistentialQuantification,FlexibleInstances, UndecidableInstances #-}

-- | A Pretty Printer for the core trellys. The 'Disp' class and
-- 'D' type should
-- be replace with their LangLib equivalents.
module Language.Trellys.PrettyPrint(Disp(..), D(..))  where

import Language.Trellys.Syntax
import Language.Trellys.GenericBind

import Generics.RepLib.R (Rep)
import Control.Monad.Reader
import Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec.Pos
import Data.Set (Set)
import qualified Data.Set as S
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

{-
-- | 'Display' is automatically lifted across pairs.
instance (Display a, Display b) => Display (a,b) where
  display (x,y) = do
      s1 <- display x
      s2 <- display y
      return $ PP.parens (s1 <> text "," <> s2)
-}

-- | 'DispElem' is used like a format string, to pretty print
--   complicated types, or long rich error messages. A whole class of
--   functions take @['DispElem']@ as input; for example, see
--   'displays', 'docM', 'stringM', 'warnM', and 'errM'.

data DispElem
  = -- | A displayable object.
    forall x . (Display x) =>  Dd x
    -- | Some literal text.
  | Ds String
    -- | Display the object, followed by a newline.
  | forall x . (Display x) => Dn x
    -- | A list of objects, separated by the given string.
  | forall x . (Display x) => Dl [x] String
    -- | A list of objects to be formatted according to the given
    --   specification, separated by the given string.
  | forall a x . Dlf (a -> [DispElem]) [a] String
    -- | A literal document.
  | D Doc
    -- | A nested list of display elements.
  | Dr [DispElem]


-- | 'displays' is the main function that combines together
-- display elements.
displays :: [DispElem] -> M [Doc]
displays xs = help (reverse xs) [] where
  help :: [DispElem] -> [Doc] -> M [Doc]
  help [] s = return s
  help ((Dr xs):ys) s = help (reverse xs++ys) s
  help (x:xs) s = do
    s2 <- case x of
        Dd y -> do y' <- display y
                   return [y']
        Ds s -> return [text s]
        Dn y -> do s <- display y
                   return [s <> text "\n"]
        D doc -> return [doc]
        Dl ys sep -> dispL display ys (text sep)
        Dlf f ys sep -> dlf f ys (text sep)
        Dr xs -> help (reverse xs) s
    help xs (s2++s)

dlf ::  (a -> [DispElem]) -> [a] -> Doc  -> M [Doc]
dlf f ys sep = do
  let elems = map f ys
  docss <- mapM displays elems
  return $ PP.punctuate sep (map PP.hcat docss)

dispL :: (a -> M Doc) -> [a] -> Doc -> M [Doc]
dispL f [] sep = return [PP.empty]
dispL f [m] sep = do { y <- f m ; return [y] }
dispL f (m:ms) sep = do
  a <- f m
  b <- dispL f ms sep
  return (a:[sep]++b)

docM :: [DispElem] -> M Doc
docM xs = do
   docs <- displays xs
   return $ PP.fsep docs

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

  disp (Sig n ep ty) =
        disp n
    <+> (case ep of {Logic -> text ":"; Program -> text ":c"})
    <+> disp ty
  disp (Axiom n ep ty) =
        text "axiom"
    <+> disp n
    <+> (case ep of {Logic -> text ":"; Program -> text ":c"})
    <+> disp ty

  disp (Data n params th lev constructors) =
    hang (disp th <+> text "data" <+> disp n <+> disp params
           <+> colon <+> text "Type" <+> text (show lev)
           <+> text "where")
           2 (vcat $ map disp constructors)
  disp (AbsData t delta th lev) =
        disp th <+> text "data" <+> disp t <+> disp delta <+> colon
    <+> text "Type" <+> text (show lev)

instance Disp Goal where
  disp (Goal ctx statement) = 
   foldr ($+$) empty (map disp ctx)
   $+$ text "========================================="
   $+$ disp statement
{-
   $+$ text "\nOr printed less prettily:"
   $+$ foldr ($+$) empty (map (text . show) ctx)
   $+$ text "========================================="
   $+$ text (show statement)
 -}

instance Disp ConstructorDef where
  disp (ConstructorDef _ c tele) = disp c <+> text "of" <+> disp tele


instance Disp ModuleImport where
  disp (ModuleImport i) = text "import" <+> disp i

instance Display Term where
  display (Var n) = display n
  display (Con n args) = do
    dn <- display n
    dargs <- mapM displayArg args
    return $ dn <+> hsep dargs
      where displayArg (t, ep) = do
                                      dt <- display t
                                      return $ wraparg t $ bindParens ep dt
  display (Type n) = return $ text "Type" <+> (text $ show n)

  display (Arrow ep bnd) = do
     lunbind bnd $ \((n,a), b) -> do
        da <- display (unembed a)
        dn <- display n
        db <- display b
        return $ (mandatoryBindParens ep $ dn  <+> colon <+> da) <+> text "->" <+> db

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

  display (Case d bnd) =
    lunbind bnd $ \ (y, alts) -> do
     dd <- display d
     dy <- display y
     dalts <- mapM displayAlt alts
     return $ text "case" <+> dd <+> (brackets dy) <+> text "of" $$
          (nest 2 $ vcat $  dalts)
    where
      displaybnd (v, ep) = do
        dv <- display v
        return $ bindParens ep dv

      displayAlt (c, bd) =
        lunbind bd $ \ (vs, ubd) -> do
              dc <- display c
              dvs <- mapM displaybnd vs
              dubd <- display ubd
              return $ (hsep (dc : dvs)) <+> text "->" <+> dubd

  display (Conv a bs bnd) =
    lunbind bnd $ \(xs,c) -> do
      da <- display a
      dbs <- mapM displayErased bs
      dxs <- mapM display xs
      dc <- display c
      return $ fsep [text "conv" <+> da,
                    text "by" <+> sep (punctuate comma dbs),
                    text "at" <+> hsep dxs  <+> text "." <+> dc]
      where displayErased (True,pf) = brackets <$> display pf
            displayErased (False, pf) = display pf

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
      return $ da  <+> text "=" <+> db
  display (Join s1 s2) =
    return $ text "join" <+> text (if s1 == s2
                            then if s1 == 100
                                   then ""
                                   else show s1
                            else show s1 ++ " " ++ show s2)
  display (Contra ty)  = do
     dty <- display ty
     return $ text "contra" <+> dty
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


-- NC copied this wrapper code from display EApp below without
-- much thought or testing ... it works pretty well down there
wraparg :: Term -> (Doc -> Doc)
wraparg x = case x of
              App _ _ _   -> parens
              Lam _ _     -> parens
              Let _ _ _   -> parens
              Case _ _    -> parens
              Con _ (_:_) -> parens
              _           -> id
wrapf :: Term -> (Doc -> Doc)
wrapf f = case f of
            Lam _ _     -> parens
            Let _ _ _   -> parens
            Case _ _    -> parens
            _           -> id

{-
epParens :: Epsilon -> [DispElem] -> DispElem
epParens Runtime l = Dd (brackets (displays l))
epParens Erased  l = Dd displays l
-}

instance Display ETerm where
  display (EVar v) = display v
  display (ECon n args) = do
    dn <- display n
    dargs <- mapM display args
    return $ dn <+> hsep dargs
      where displayArg (t, ep) = do dt <- display t
                                    return $ bindParens ep dt
  display (EType level) = return $ text "Type" <+> integer level
  display (EArrow ep a bnd) = do
     da <- display a
     lunbind bnd $ \ (n,b) -> do
        dn <- display n
        db <- display b
        return $ (mandatoryBindParens ep $ dn <+> text ":" <+> da) <+>
                    text "->" <+> db
  display (ELam  b) =
     lunbind b $ \ (n, body) -> do
       dn <- display n
       dbody <- display body
       return ( text "\\" <+> dn <+> text "." <+> dbody )
  display (EApp f x) = do
       df <- display f
       dx <- display x
       let wrapx = case x of
                     EApp _ _  -> parens
                     ELam _    -> parens
                     ELet _ _  -> parens
                     ECase _ _ -> parens
                     _         -> id
       let wrapf = case f of
                     ELam _    -> parens
                     ELet _ _  -> parens
                     ECase _ _ -> parens
                     _         -> id
       return (wrapf df <+> wrapx dx)
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
  display (ERecMinus bnd) =
     lunbind bnd $ \ (n,body) -> do
        dn <- display n
        db <- display body
        return $ parens ( text "rec" <+> dn
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

