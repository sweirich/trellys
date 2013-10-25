{-# LANGUAGE  ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing #-}

-- Functions to extract OCaml code from Trellys definitions.

module Language.Trellys.Extraction (extractModules) where

import Language.Trellys.GenericBind
import Language.Trellys.Syntax
import Language.Trellys.TypeMonad
import Language.Trellys.Environment
import Language.Trellys.Error
import Language.Trellys.OpSem (eraseToHead)
import Language.Trellys.TypeCheckCore

import Text.PrettyPrint.HughesPJ as PP
import Control.Applicative ((<$>))

extractTermName :: AName -> Doc
extractTermName x = text ("tm_" ++ show x)

extractTypeName :: AName -> Doc
extractTypeName x = text ("'ty_" ++ show x)

extractTConName :: AName -> Doc
extractTConName d = text ("tcon_" ++ show d)

extractDConName :: AName -> Doc
extractDConName c = text ("Dcon_" ++ show c)

commaSeparated :: [Doc] -> Doc 
commaSeparated [] = empty
commaSeparated [d] = d
commaSeparated ds = parens (hsep (punctuate comma ds))

isInformative :: ATerm -> Bool
isInformative (eraseToHead -> AType _) = False
isInformative (eraseToHead -> ATyEq _ _) = False
isInformative (eraseToHead -> ASmaller _ _) = False
isInformative _ = True

extractTerm :: ATerm -> TcMonad Doc
extractTerm a = do
  (_,aTy) <- getType a
  if isInformative aTy
   then extractTerm' a
   else return $ text "()"
 where
  extractTerm' :: ATerm -> TcMonad Doc
  extractTerm' (AVar x) = return $ extractTermName x
  extractTerm' (AUniVar ux _) = err [DS "internal error: extraction encountered unbound univar"]
  extractTerm' (ADCon c th params args) = do
    eargs <- mapM (extractTerm . fst) (filter ((== Runtime) . snd) args)
    return . parens $
      extractDConName c <+> commaSeparated eargs
  extractTerm' (ALam th (eraseToHead -> (AArrow _ _ _ bndTy)) ep bnd) = do
    Just ((x , unembed -> aTy), bodyTy , _, body) <- unbind2 bndTy bnd
    ebody <- extendCtx (ASig x Program aTy) $ extractTerm body
    return $ parens (text "function" <+> extractTermName x <+> text "->" <+> ebody)
  extractTerm' (AApp Runtime a b ty) = do
    ea <- extractTerm a
    eb <- extractTerm b
    return $ parens (ea <+> eb)
  extractTerm' (AApp Erased a b ty) = do
    ea <- extractTerm a
    return $ parens (ea <+> text "()")
  extractTerm' (AUnbox a) = extractTerm' a
  extractTerm' (ABox a th) = extractTerm' a
  extractTerm' (AAbort ty) = return $ parens (text "raise Abort")
  extractTerm' (AConv a pf) = do
    ea <- extractTerm a
    --todo: figure out when to insert a cast like this.
    --return $ parens (text "Obj.magic" <+> ea)
    return ea
  extractTerm' (AContra pf ty) = return $ parens (text "raise Contra")
  extractTerm' (AInd ty ep bnd) =
    underInd (AInd ty ep bnd) 
             (\x f body -> do
               y <- fresh (string2Name "y")
               g <- fresh (string2Name "g")
               ebody <- extractTerm body
               return . parens $
                  vcat [text "let rec" 
                         <+> extractTermName f <+> extractTermName x <+> text "_" <+> text "=",
                        nest 10 ebody,
                        text "    and" 
                         <+> extractTermName g <+> extractTermName y <+> text "=",
                        nest 10 (extractTermName f <+> extractTermName y <+> text "()"),
                        text "in",
                           nest 2 (extractTermName g)])
  extractTerm' (ARec ty ep bnd) =
    underRec (ARec ty ep bnd) 
             (\x f body -> do
               ebody <- extractTerm body
               return . parens $
                 vcat [text "let rec"
                         <+> extractTermName f <+> extractTermName x <+> text "=",
                         nest 10 ebody,
                         text "in",
                         nest 2 (extractTermName f)])
  extractTerm' t@(ALet Erased _ _) = do
    underLet t (\x xeq body -> extractTerm body)
  extractTerm' t@(ALet Runtime bnd _) = do
    ((_, _, unembed -> val), _) <- unbind bnd
    eval <- extractTerm val
    underLet t (\x eq body -> do
                   ebody <- extractTerm body
                   return . parens $
                     hsep [text "let" <+> extractTermName x <+> text "=",
                           nest 2 eval,
                           text "in",
                           nest 2 ebody])
  extractTerm' t@(ACase a bnd (th,ty)) = do
    (xeq, mtchs) <- unbind bnd
    ea <- extractTerm a
    emtchs <- underCase t extractMatch
    return $ parens (hang (text "match" <+> ea <+> text "with")
                          2
                          (vcat emtchs))                           
  extractTerm' (ATrustMe ty) = return $ parens (text "raise Trustme")
  extractTerm' a = err [DS "internal error: extractTerm' called on a noninformative subterm.", DD a]

extractMatch :: AName -> ATelescope -> ATerm -> TcMonad Doc
extractMatch c xs body = do
  ebody <- extractTerm body
  return $
    text "|" <+> extractDConName c 
             <+> commaSeparated (extractNames extractTermName xs)
             <+> text "->"
     $$ (nest 2 ebody)

extractNames :: (AName -> Doc) -> ATelescope -> [Doc]
extractNames extractName (ACons (unrebind->((x, _, ep), xs))) = do
  if (ep == Runtime)
    then extractName x : extractNames extractName xs
    else extractNames extractName xs
extractNames extractName AEmpty = []

extractType :: ATerm -> TcMonad Doc
extractType a = do
  (_,aTy) <- getType a
  case eraseToHead aTy of 
   AType _ -> extractType' a
   _       -> return $ text "unit"
 where
    extractType' :: ATerm -> TcMonad Doc
    extractType' (AVar x) = return $ extractTypeName x
    extractType' (AUniVar ux _) = err [DS "internal error: extractType encountered unbound univar"]
    extractType' (ACumul _ _) = return $ text "unit"
    extractType' (AType lvl) = return $ text "unit"     
    extractType' (ATCon c params) = do
      eparams <- mapM extractType params
      return $ parens (commaSeparated eparams <+> extractTConName c)
    extractType' (AArrow lvl ex ep bnd) = do
      ((x, unembed->a),b) <- unbind bnd
      ea <- extractType a
      eb <- extendCtx (ASig x Program a) $ extractType b
      return $ parens (ea <+> text "->" <+> eb)
--Note that this will take applications of type-level lambdas to
-- just "unit", which requires patching with Obj.magic later. 
-- Similarly for case and let.
-- On the other hand, application of datatype constructors is handled.
    extractType' (AApp ep a b ty) = return $ text "unit"
    extractType' (ALet ep bnd (th,val)) = return $ text "unit"
    extractType' (ACase a bnd (th,ty)) = return $ text "unit"
    extractType' (AAt a th) = extractType a
    extractType' (AUnbox a) = extractType a
    extractType' (ABox a th) = extractType a
    extractType' (ATyEq a b) = return $ text "unit"
    extractType' (AConv a pf) = error "extracting conv type?" --fixme: not sure what to do here
    extractType' (ASmaller a b) = return $ text "unit"
    extractType' (AAbort ty) = err [DS "Can't extract abort in a type position"]
    extractType' (ATrustMe ty) = err [DS "Can't extract TRUSTME in a type position"]
    extractType' _ = err [DS "internal error: extractType' called on a a non-typeformer"]

extractConstructorDef :: AConstructorDef -> TcMonad Doc
extractConstructorDef (AConstructorDef c args) = do
  eargs <- extractTypes args
  return $ text "|" <+> extractDConName c
           <+> (if null eargs 
                 then empty
                 else text "of" <+> (hsep (punctuate (text " *") eargs)))
 where extractTypes :: ATelescope -> TcMonad [Doc]
       extractTypes AEmpty = return []
       extractTypes (ACons (unrebind->((x, unembed->ty, Erased), xs))) =
         extendCtx (ASig x Program ty) $
           extractTypes xs
       extractTypes (ACons (unrebind->((x, unembed->ty, Runtime), xs))) = do
         ety <- extractType ty
         exs <- extendCtx (ASig x Program ty) $
                  extractTypes xs
         return $ ety : exs         

extractDecl :: ADecl -> TcMonad Doc
extractDecl (ASig x th a) = return empty
extractDecl (ADef x a) = do
  ea <- extractTerm a
  return $ hang (text "let" <+> extractTermName x <+> text "=")
                2 
                ea
extractDecl (AData d params lvl []) = do
   return $ hang (text "type"
                   <+> commaSeparated (extractNames extractTypeName params)
                   <+> extractTConName d <+> text "=")
                  2
                  (text "Dummy_" <> extractTConName d 
                   <+> text "(* Hack since OCaml doesn't like empty data types *)")
extractDecl (AData d params lvl cons) = do
   econs <- extendCtx (AAbsData d params lvl) $
              extendCtxTele params Program $
                mapM extractConstructorDef cons
   return $ hang (text "type" 
                    <+> commaSeparated (extractNames extractTypeName params)
                    <+> extractTConName d <+> text "=")
                 2
                 (vcat econs)
extractDecl (AAbsData _ _ _) = error "internal error: extractDecl called on AAbsData"

extractDecls :: [ADecl] -> TcMonad Doc
extractDecls (d:ds) = do
  ed <- extractDecl d
  eds <- extendCtx d $ extractDecls ds
  return (ed $+$ eds)
extractDecls [] = return empty

extractionPreamble :: Doc
extractionPreamble =
      text "exception Abort"
  $+$ text "exception Contra"
  $+$ text "exception Trustme\n\n"
        
extractModules :: [AModule] -> TcMonad Doc
extractModules mods = 
  (extractionPreamble $+$) <$> extractDecls (concatMap aModuleEntries mods)
