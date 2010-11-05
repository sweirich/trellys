{-# LANGUAGE StandaloneDeriving, TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
    UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Trellys.GenericBind (Fresh(..),Alpha(..),HasNext(..), LFresh(..)
  ,AlphaCtx
  ,Name,rName,name1,name2,name3,name4,name5
  ,name2Integer,integer2Name,string2Name
  ,binders,patfv,fv,swaps
  ,aeq
  ,Bind,rBind,bind,unbind,unbind2,unbind3
  ,Rebind,rRebind,rebind,reopen
  ,Annot(..),rAnnot
  ,Subst(..), matchR1
  ,unsafeUnBind
  ,lunbind
  ,abs_swaps',abs_fv',abs_freshen',abs_match'
  ,abs_nthpatrec,abs_findpatrec,abs_close,abs_open  -- only for LocallyNameless
--  ,subst,substs -- only for Nominal
  ,rSourcePos
)  where

-- To switch between LocallyNameless and Nominal versions of the binding library:
-- (1) change the import statement below from LocallyNameless to Nominal
-- (2) adjust the exports above  
-- (3) change the Alpha and Subst instances for SourcePos below

import Data.RepLib.Bind.LocallyNameless

import Data.RepLib hiding (Arrow)
import Text.ParserCombinators.Parsec.Pos

-- We define an rSourcePos, which then allows us to use derive for
-- expressions that include SourcePos's directly.
rSourcePos :: R a
rSourcePos = Data (DT "SourcePos" MNil) [error "rSourcePos: SourcePos is abstract"]

instance Rep SourcePos where rep = rSourcePos
instance (Sat (ctx SourcePos)) => Rep1 ctx SourcePos where
   rep1 = Data1 (DT "SourcePos" MNil) [error "rep1: SourcePos is abstract"]



-- Alpha for source positions (cannot be derived b/c type is abstract)
instance Alpha SourcePos where
  swaps'      = abs_swaps'
  fv'         = abs_fv'
  freshen'    = abs_freshen'
  match'      = abs_match'
-- only for locally nameless
  nthpatrec  = abs_nthpatrec
  findpatrec = abs_findpatrec
  close      = abs_close
  open       = abs_open

instance Subst b SourcePos where
  isvar _ = Nothing
{- --nominal version
  lsubst _ _ s = return s
  lsubsts _ _ s = return s
-}
  -- locally nameless version 
  subst _ _ s = s
  substs _ _ s = s


     