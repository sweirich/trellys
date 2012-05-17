-- | This module provides a basic error reporting facility. It should be removed
-- in lieu of the LangLib implementation.
{-# LANGUAGE FlexibleContexts, GADTs, RankNTypes #-}
module Language.Trellys.Error
  (SourceLocation(..),Err(..), D(..)) where

import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint

import Control.Monad.Error
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos(SourcePos)

data SourceLocation where
  SourceLocation :: forall a. Disp a => SourcePos -> a -> SourceLocation

-- The error disp only shows the first context, not all of it.
data Err = Err [SourceLocation] Doc
instance Disp Err where
  disp (Err [] msg) = msg
  disp (Err ((SourceLocation p term):_) msg)  =
    disp p $$
    nest 2 msg $$
    nest 2 (text "In the expression" $$ nest 2 (disp term))

instance Error Err where
  strMsg msg = Err [] (text msg)
