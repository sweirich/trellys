-- | This module provides a basic error reporting facility. It should be removed
-- in lieu of the LangLib implementation.
{-# LANGUAGE FlexibleContexts #-}
module Language.Trellys.Error
  (err, Err(..), D(..)) where

import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint

import Control.Monad.Error
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos(SourcePos)

-- The error disp only shows the first context, not all of it.
data Err = Err [(SourcePos,Term)] Doc
instance Disp Err where
  disp (Err [] msg) = msg
  disp (Err [(p,term)] msg)  =
    disp p $$
    nest 4 msg $$
    nest 4 (text "In the expression " <+> disp term)
  disp (Err ((_,term):ps) msg)  =
    disp (Err ps msg) $$
    (nest 4 (text "In the expression " <+> disp term))


instance Error Err where
  strMsg msg = Err [] (text msg)

err :: (Disp a,MonadError Err m) => a -> m b
err d = throwError $ Err [] (disp d)

