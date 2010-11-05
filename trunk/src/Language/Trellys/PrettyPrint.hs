{-# LANGUAGE TypeSynonymInstances,ExistentialQuantification,FlexibleInstances #-}

-- | A Pretty Printer for the core trellys. The 'Disp' class and 'D' type should
-- be replace with their LangLib equivalents.
module Language.Trellys.PrettyPrint(Disp(..), D(..))  where

import Language.Trellys.Syntax
import Language.Trellys.GenericBind hiding (avoid)

import Control.Monad.Reader
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos
import Data.Set (Set)
import qualified Data.Set as S

-- | Convert to a formatted 'Doc'. FIXME: Needs to be made monadic, so that
-- 'Name's can be displayed correctly.
class Disp d where
  disp :: d -> Doc

-- This function tries to pretty-print terms using as little renaming
-- of variables as possible.
cleverDisp :: (Disp' d, Alpha d) => d -> Doc 
cleverDisp d = 
  let pc = PPContext{currentAvoid = S.empty}
      -- bind then unbind in order to pick "better" names for
      -- free variables.
      vars = S.elems (fv d)
      (vars', d') = unbindAvoiding pc (bind vars d)
      pc' = avoid vars' pc
  in  
    disp' pc' d'

instance Disp Term where
  disp = cleverDisp
instance Disp ETerm where
  disp = cleverDisp
instance Disp Name where
  disp = cleverDisp
instance Disp  Telescope where
  disp = cleverDisp

-- In a more perfect world this would also include the current precedence
-- level, so we could print parenthesis exactly when needed.
data PPContext = PPContext { currentAvoid :: Set Name }

class Disp' d where
  disp' :: PPContext -> d -> Doc

unbindAvoiding :: (Alpha a, Alpha b) => PPContext -> Bind a b -> (a, b)
unbindAvoiding pc b  = runReader (lunbind b) (currentAvoid pc)

avoid :: [Name] -> PPContext -> PPContext
avoid ns pc = pc { currentAvoid = (currentAvoid pc) `S.union` (S.fromList ns) }

thetaArrow :: Theta -> Doc
thetaArrow Logic = text "->"
thetaArrow Program = text "=>"

bindParens :: Epsilon -> Doc -> Doc
bindParens Runtime d = d
bindParens Erased  d = brackets d


instance Disp Module where
  disp m = text "module" <+> disp (moduleName m) <+> text "where" $$
           vcat (map disp (moduleImports m)) $$
           vcat (map disp (moduleEntries m))

instance Disp Decl where
  disp (Def _ r@(NatRec _ _)) = disp r
  disp (Def _ r@(Rec _ _)) = disp r
  disp (Def n term) = disp n <+> text "=" <+> disp term

  disp (Sig n ep ty) =
        disp n
    <+> (case ep of {Logic -> text ":"; Program -> text ":c"})
    <+> disp ty
  disp (Data n params th lev constructors) =
    hang (text "data" <+> disp n <+> disp params
           <+> thetaArrow th <+> text "Type" <+> text (show lev)
           <+> text "where")
           2 (vcat $ map disp constructors)
  disp (AbsData t delta th lev) =
        text "data" <+> disp t <+> disp delta <+> thetaArrow th
    <+> text "Type" <+> text (show lev)


instance Disp ModuleImport where
  disp (ModuleImport i) = text "import" <+> disp i

instance Disp' Term where
  disp' pc (Var n) = disp' pc n
  disp' pc (Con n) = disp' pc n
  disp' pc (Type n) = text "Type" <+> (text $ show n)

  disp' pc (Arrow th ep a bnd) =
         (bindParens ep $ disp' pc n <+> colon <+> disp' pc a)
     <+> thetaArrow th <+> disp' (avoid [n] pc) b
   where (n,b) = unbindAvoiding pc bnd

  disp' pc (Lam ep b) =
    text "\\" <+> bindParens ep (disp' pc n) <+> text "." <+> disp' (avoid [n] pc) body
   where (n,body) = unbindAvoiding pc b

  disp' pc (NatRec ep binding) =
    let ((n,x),body) = unbindAvoiding pc binding
    in     text "recnat" <+> disp' pc n <+> bindParens ep (disp' pc x) <+> text "="
       <+> disp' (avoid [n,x] pc) body

  disp' pc (Rec ep binding) =
    let ((n,x),body) = unbindAvoiding pc binding
    in     text "rec" <+> disp' pc n <+> bindParens ep (disp' pc x) <+> text "="
       <+> disp' (avoid [n,x] pc) body

  disp' pc (App ep e1 e2) = disp' pc e1 <+> (bindParens ep $ disp' pc e2)
  disp' pc (Paren e) = parens $ disp' pc e
  disp' pc (Pos _ e) = disp' pc e

  disp' pc (Let th ep a bnd) =
         text "let" <+> tag <+> bindParens ep (disp' pc x) <+> brackets (disp' pc y)
     <+> text "=" <+> disp' pc a <+> text "in" <+> disp' (avoid [x,y] pc) b
     where
       ((x,y),b) = unbindAvoiding pc bnd
       tag = case th of {Logic -> text ""; Program -> text "prog"}

  disp' pc (Case d bnd) =
     text "case" <+> disp' pc d <+> (brackets (disp' pc y)) <+> text "of" $$
          (nest 2 $ vcat $  map (disp'Alt (avoid [y] pc)) alts)
    where
      (y,alts) = unbindAvoiding pc bnd

      disp'bnd pc (v, ep) = bindParens ep $ disp' pc v

      disp'Alt pc (c, bd) =
        let (vs,ubd) = unbindAvoiding pc bd in
              hsep (disp' pc c : map (disp'bnd pc) vs)
          <+> text "->" <+> disp' (avoid (map fst vs) pc) ubd

  disp' pc (Conv a b bnd) =
    text "conv" <+> disp' pc a <+> text "by" <+> disp' pc b <+> text "at"
                <+> disp' pc x <+> text "." <+> disp' (avoid [x] pc) c
    where
      (x,c) = unbindAvoiding pc bnd

  disp' pc (TyEq a b)   = disp' pc a <+> text "=" <+> disp' pc b
  disp' pc (Join s1 s2) =
    text "join" <+> text (if s1 == s2
                            then if s1 == 100
                                   then ""
                                   else show s1
                            else show s1 ++ " " ++ show s2)
  disp' pc (Contra ty)  = text "contra" <+> disp' pc ty
  disp' pc Abort        = text "abort"
  disp' pc (Ann a b)    = parens (disp' pc a <+> text ":" <+> disp' pc b)


instance Disp' ETerm where
  disp' pc (EVar v) = disp' pc v
  disp' pc (ECon v) = disp' pc v
  disp' pc (EType level) = text "Type" <+> int level
  disp' pc (EArrow th ep a bnd) =
         (bindParens ep $ disp' pc n <+> colon <+> disp' pc a)
     <+> thetaArrow th <+> disp' (avoid [n] pc) b
   where (n,b) = unbindAvoiding pc bnd
  disp' pc (ELam  b) =
    text "\\" <+> (disp' pc n) <+> text "." <+> disp' (avoid [n] pc) body
   where (n,body) = unbindAvoiding pc b
  disp' pc (EApp f x) = disp' pc f <+> disp' pc x
  disp' pc (ETyEq e0 e1) = disp' pc e0 <+> text "=" <+> disp' pc e1
  disp' pc EJoin = text "join"
  disp' pc EAbort = text "abort"
  disp' pc (ERecPlus bnd) =
      parens $ text "rec" <+> disp' pc n <+> brackets (disp' pc w) <+> text "." 
                <+> disp' (avoid [n,w] pc) body
    where ((n,w),body) = unbindAvoiding pc bnd
  disp' pc (ERecMinus bnd) =
      parens $ text "rec" <+> disp' pc n <+>  text "." <+> disp' (avoid [n] pc) body
    where (n,body) = unbindAvoiding pc bnd
  disp' pc (ECase dis matches) = nest 2
    (text "case" <+> disp' pc dis <+> text "of" $$
    nest 2 (vcat (map (disp' pc) matches)))
  disp' pc (ELet val bnd) =
      text "let" <+> disp' pc n <+> text "=" <+> disp' pc val $$
      text "in" <+> disp' (avoid [n] pc) body
    where (n,body) = unbindAvoiding pc bnd
  disp' pc EContra = text "contra"


instance Disp' EMatch where
  disp' pc (n,bnd) = disp' pc n <+> pat <+> text "->" <+> disp' (avoid vars pc) body
    where (vars,body) = unbindAvoiding pc bnd
          pat = hcat $ punctuate space $ map (disp' pc) vars




instance Disp Epsilon where
  disp Erased = text "-"
  disp Runtime = text "+"

instance Disp' Telescope where
  disp' pc ts =
    hcat $ [prns ep $ disp' pc n <+> colon <+> disp' pc ty <+> thetaArrow th
              | (n,ty,th,ep) <- ts]
    where prns Runtime = parens
          prns Erased = brackets

instance Disp Theta where
  disp Logic = text "L"
  disp Program = text "P"

-- Assumes that all terms were opened safely earlier.
instance Disp' Name where
  disp' pc = text . show

instance Disp SourcePos where
  disp p = text (sourceName p) <> colon <> int (sourceLine p) <>
           colon <> int (sourceColumn p) <> colon

-- | Error message quoting
data D = DS String -- ^ String literal
       | forall a . Disp a => DD a -- ^ Displayable value

instance Disp D where
  disp (DS s) = text s
  disp (DD d) = quotes $ disp d

instance Disp [D] where
  disp dl = sep $ map disp dl

instance Disp [Term] where
  disp = vcat . map disp

instance Disp [(Name,Term)] where
  disp = vcat . map disp

instance Disp (Name,Term) where
  disp (n,t) = parens $ (disp n) <> comma <+> disp t

