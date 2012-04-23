-- | This module provides a basic error reporting facility. It should be removed
-- in lieu of the LangLib implementation.
{-# LANGUAGE FlexibleContexts #-}
module Language.Trellys.Error
  (Err(..), D(..)) where

import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint

import Control.Monad.Error
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos(SourcePos)

-- The error disp only shows the first context, not all of it.
data Err = Err [(SourcePos,Term)] Doc
instance Disp Err where
  disp (Err [] msg) = msg
  disp (Err ((p,term):_) msg)  =
    disp p $$
    nest 2 msg $$
    nest 2 (text "In the expression" $$ nest 2 (disp term))
--  disp (Err ((_,term):ps) msg)  =
--    disp (Err ps msg) $$
--    (nest 2 (text "In the expression" $$ nest 2 (disp term)))


instance Error Err where
  strMsg msg = Err [] (text msg)

