{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances, UndecidableInstances, PackageImports #-}
module Language.SepPP.PrettyPrint where

import Language.SepPP.Syntax

import Unbound.LocallyNameless hiding (empty,Val,Con,Refl,Equal)

import Text.PrettyPrint
import Control.Applicative hiding (empty)
import "mtl" Control.Monad.Reader
import Text.Parsec.Pos
import Text.Parsec.Error(ParseError,showErrorMessages,errorPos,errorMessages)
import qualified Data.Set as S


class Disp d where
  disp :: d -> Doc


instance Disp Doc where
  disp = id
instance Disp String where
  disp  = text
instance Disp Expr where
  disp  = cleverDisp
instance Disp EExpr where
  disp = cleverDisp
instance Rep a => Disp (Name a) where
  disp = cleverDisp
instance Disp Module where
  disp = cleverDisp
instance Disp Int where
  disp = integer . toInteger

instance Disp Tele where
  disp = cleverDisp



instance Disp (Maybe Expr) where
  disp = maybe empty disp


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
barenames :: Bool
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



cleverDisp :: (Display d, Alpha d) => d -> Doc
cleverDisp d =
  runReader (runFreshMT dm) initDI where
    dm = let vars = S.elems (fvAny d)  in
         lfreshen vars $ \_  p ->
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

instance Rep a => Display (Name a) where
  display = return . text . name2String

instance Display Expr where
  display WildCard = return $ text "_"
  display (Var n) = return $ text $ name2String n
  display (Con n) = return $ text $ name2String n
  display (Formula 0) = return $ text "Formula"
  display (Formula n) = return $ text "Formula" <+> integer n
  display Type = return $ text "Type"

  display (Pi stage binding) = do
      lunbind binding fmt
    where fmt ((n,ty,inf),ran) = do
                        dn <- display n
                        dty <- display ty
                        dran <- display ran
                        let dinf = if inf then text "?" else empty
                        return $ bindingWrap stage (dinf <+> dn <+> colon <+> dty) <+> text "->" <+> dran


  display (Forall binding) = 
    lunbind binding $ \((n,ty,inf),ran) -> do
      dn <- display n
      dty <- display ty
      dran <- display ran
      let dinf = if inf then text "?" else empty
      return $ text "forall" <+> parens (dinf <+> dn <+> colon <+> dty) <+> text "." <+> dran

  display (t@(App t0 stage t1)) = do
    d0 <- dParen (precedence t - 1) t0
    d1 <- dParen (precedence t) t1
    return $ d0 <+> ann stage d1
   where ann Static = brackets
         ann Dynamic = id


  display (Lambda kind stage binding) = 
    lunbind binding $ \((n,ty),body) -> do
      dty <- display ty
      dn <- display n
      dbody <- display body
      return $ text "\\" <+> bindingWrap stage (dn <+> colon <+> dty) <+>
               absOp kind <+> dbody

    where absOp Form = text "=>"
          absOp Program = text "->"

  display (Case scrutinee termWitness binding) =
   lunbind binding $ \(consEq,alts) -> do
    dScrutinee <- display scrutinee
    dConsEq <- braces <$> display consEq
    dTermWitness <- maybe (return empty) display termWitness
    dAlts <- mapM dAlt alts
    return $ text "case" <+> dScrutinee <+> dConsEq <+> dTermWitness <+> text "of" $$
             nest 2 (vcat dAlts)

    where dAlt alt = do
            lunbind alt $ \((con,pvars),body) -> do
             dPvars <- mapM dPVar pvars
             dBody <- display body
             return $ cat [text con <+> hsep dPvars <+> text "-> ",
                          nest 2 dBody]
          dPVar (v,Static) = return $ brackets $ disp v
          dPVar (v,Dynamic) = return $ brackets $ disp v


  display (TerminationCase scrutinee binding) =
    lunbind binding $ \(n,(diverge,terminate)) -> do
                        dScrutinee <- display scrutinee
                        dDiverge <- display diverge
                        dTerminate <- display terminate
                        dn <- display n
                        return $ hang (text "termcase" <+> dScrutinee <+> braces dn <+> text "of") 2
                                 (braces (text "abort" <+> text "->" <+> dDiverge <> semi $$
                                          text "!" <+> text "->" <+> dTerminate))


  display (Join i0 i1) =
    return $ text "join" <+> integer i0 <+> integer i1


  display (t@(Equal t0 t1)) = do
                     d0 <- dParen (precedence t) t0
                     d1 <- dParen (precedence t) t1
                     return $ fsep [d0, text "=", d1]

  display (w@(Val t)) = do
    d <- termParen (precedence w) t
    return $ text "valax" <+> d

  display (w@(Terminates t)) = do
                     dt <- termParen (precedence w) t
                     return $ dt <+> text "!"


  display w@(TCast t p) = do
    dt <- termParen (precedence w) t
    dp <- termParen (precedence w) p
    return $ text "tcast" <+> dt <+> text "by" <+> dp



  display (t@(Contra t0)) = do
    d0 <- termParen (precedence t) t0
    return $ text "contra" <+> d0

  display (t@(ContraAbort t0 t1)) = do
    d0 <- termParen (precedence t) t0
    d1 <- termParen (precedence t) t1
    return $ text "contraabort" <+> d0 <+> d1

  display (w@(Abort t)) = do
    d <- dParen (precedence w) t
    return $ text "abort" <+> d

  display (w@(Show t)) = do
    d <- dParen (precedence w) t
    return $ text "show" <+> d

  display (Conv t pfs binding) = do
    lunbind binding $ \(vars,ty) -> do
      dVars <- mapM display vars
      dTy <- display ty
      dt <- display t
      dPfs <- mapM display pfs
      return $ fsep ([text "conv" <+> dt, text "by"] ++
                    (punctuate comma dPfs) ++
                    [text "at"] ++
                    dVars ++
                    [text ".", dTy])

  -- Context-style conversions
  display (ConvCtx t ctx) = do
    dt <- display t
    dctx <- display ctx
    return $ fsep [text "conv",nest 5 dt,text "at",nest 3 dctx]


  display (Escape t) = do
    dt <- display t
    return $ text "~" <> dt


  display (t@(Ord t0)) = do
    d0 <- termParen (precedence t) t0
    return $ text "ord" <+> d0

  display (t@(OrdTrans t0 t1)) = do
    d0 <- termParen (precedence t) t0
    d1 <- termParen (precedence t) t1
    return $ text "ordtrans" <+> d0 <+> d1


  display (t@(IndLT t0 t1)) = do
     d0 <- dParen (precedence t) t0
     d1 <- dParen (precedence t) t1
     return (d0 <+> text "<" <+> d1)



  display (Ind binding) = do
   lunbind binding $ \((f,tele,u),body) -> do
     df <- display f
     -- dx <- display x
     -- dTy <- display ty
     dtele <- display tele
     dBody <- display body
     du <- display u
     return $
      fsep [text "ind" <+> df <+> dtele <+>
           brackets du <+> text ".",
           nest 2 dBody]


  display (Rec binding) = do
    lunbind binding $ \((f,tele),body) -> do
      df <- display f
      dtele <- display tele
      dBody <- display body
      return $
         sep [text "rec" <+> df <+> dtele <+>
              text ".",
              nest 2 dBody]


  display (t@(Let _ _)) = do
    (ds,body) <- linearizeLet t
    let f (stage', (x,y,Embed z))= do
            dx <- case stage' of
               Static -> brackets <$> display x
               Dynamic -> display x
            dy <- case y of
                    Just var -> brackets <$> display var
                    Nothing -> return empty
            dz <- display z
            return (sep [dx <+> dy <+> text "=",nest 3 dz])
    docs <- mapM f ds
    db <- display body
    return $ sep
      [text "let" <+> nest 4 (sep (punctuate (text ";") docs)), text "in" <+> db]


  display (t@(Aborts c)) = do
    dc <- dParen (precedence t) c
    return $ text "aborts" <+> dc
  display (t@(Ann t0 t1)) = do
    d0 <- dParen (precedence t) t0
    d1 <- dParen (precedence t) t1
    return $ fsep [d0, colon, nest 2 d1]


  display (Exists binding) =
    lunbind binding $ \((n,Embed ty),body) -> do
      dn <- display n
      dty <- display ty
      dbody <- display body
      return $ fsep [text "exists", dn, colon, dty, text ".", dbody]

  display (EIntro e1 e2) = do
    d1 <- display e1
    d2 <- display e2
    return $ parens (d1 <> comma <+> d2)

  display (EElim scrutinee binding) =
    lunbind binding $ \((l,r),body) -> do
      ds <- display scrutinee
      dl <- display l
      dr <- display r
      dbody <- display body
      return $ text "unpack" <+> ds <+> text "as" <+>
                parens (dl <> comma <+> dr) <+> text "in" $$
               nest 2 dbody
  display (Pos _ t) = display t


  display (Tactic t) = display t

  -- display e = error $ "display: " ++ show e

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
  precedence (Tactic t) = precedence t

  precedence (Pi Dynamic _) = 4
  precedence (Pi Static _) = 4
  precedence _ = 0



instance Display Tactic where
  display t@(Sym x) = do
    dx <- dParen (precedence t) x
    return $ text "sym" <+> dx

  display (Equiv x) = do
    return $ text "equiv" <+> integer x

  display (t@(Autoconv x)) = do
    dx <- dParen (precedence t) x
    return $ text "autoconv" <+> dx


  display Refl = return $ text "refl"
  display t@(Trans t1 t2) = do
    d1 <- dParen (precedence t) t1
    d2 <- dParen (precedence t) t2
    return $ text "trans" <+> d1 <+> d2

  display (MoreJoin xs) = do
    ds <- mapM display xs
    return $ text "morejoin" <+> braces (hcat (punctuate comma ds))

  display (t@(Injective x)) = do
    dx <- dParen (precedence t) x
    return $ text "injective" <+> dx
    

  precedence (Sym _) = 5
  precedence (Trans _ _) = 5
  precedence Refl = 5
  precedence (Equiv _) = 5
  precedence (MoreJoin _) = 5
  precedence (Autoconv _) = 5
  precedence (Injective _) = 5
  

linearizeLet :: 
  LFresh m => Expr -> m ([(Stage, (EName, Maybe EName, Embed Expr))], Expr)

linearizeLet (Pos _ t) = linearizeLet t
linearizeLet (Let stage binding) =
  lunbind binding $ \(triple,body) -> do
     (ds,b) <- linearizeLet body
     return((stage,triple):ds,b)
linearizeLet x = return ([],x)

-- bindingWrap adds the correct stage annotation for an abstraction binding.
bindingWrap :: Stage -> Doc -> Doc
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


  display (FlagDecl n val) =
    return $ text "flag" <+> text n <+> (if val then text "true" else text "false")
  display (OperatorDecl fx level op) =
    return $ text fx <+> int level <+> text op
    


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
  display (ERec binding) = do
    lunbind binding $ \((f,_args),_body) -> do
      df <- display f
      return df    
    -- dx <- mapM display args
    -- dbody <- etermParen (precedence t) body
    -- return $ text "rec" <+> df <+> (hcat dx) <+> text "." <+> dbody


  display t@(ELambda binding) =  
    lunbind binding $ \(x,body) -> do
     dx <- display x
     dbody <- etermParen (precedence t) body
     return $ fsep [text "\\" <+> dx <+> text ".",nest 2 dbody]

  display (ECase s alts) = do
    ds <- display s
    dalts <- mapM displayAlt alts
    return $ text "case" <+> ds <+> text "of" $$
             nest 2 (vcat dalts)
   where displayAlt alt = 
            lunbind alt $ \((c,pvars),body) -> do
              dbody <- display body
              dpvars <- mapM display pvars
              return $ fsep $ [text c <+> hsep dpvars <+> text "->", nest 2 dbody]

  display (ELet binding) = 
     lunbind binding $ \((n,t),body) -> do
      dn <- display n
      dt <- display t
      dbody <- display body
      return $ text "let" <+> dn <+> text "=" <+> dt $$
               text "in" <+> dbody
  display (EPi stage binding) = 
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
