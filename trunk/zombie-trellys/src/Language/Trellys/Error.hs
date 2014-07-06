-- | This module provides a basic error reporting facility. 
-- It should be removed in lieu of the LangLib implementation.
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, RankNTypes #-}
module Language.Trellys.Error
  (SourceLocation(..),Err(..), D(..), rethrowWith) where

import Language.Trellys.Syntax
import Language.Trellys.PrettyPrint

import Control.Monad.Error
import Data.Maybe (isNothing)
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos(SourcePos)

data SourceLocation where
  SourceLocation :: forall a. Disp a => Maybe SourcePos -> a -> SourceLocation

sourceLocationPos :: SourceLocation -> Maybe SourcePos
sourceLocationPos (SourceLocation pos _) = pos



-- The error disp only shows the first context, not all of it.


data Err = Err [SourceLocation] Doc
instance Disp Err where
  disp (Err locs msg) = 
    (case pos of 
      Just p -> disp p
      Nothing -> text "unknown location:0:0") $$
    nest 2 msg $$
    nest 2 (disp traceBack)
   where pos = msum $ map sourceLocationPos locs                    -- The first defined position
         traceBack = takeWhile1 (isNothing.sourceLocationPos) locs  -- Context until we find a position

-- Shows just the expression part.
instance Disp [SourceLocation] where
  disp locs =
    vcat $ map (\(SourceLocation _ a) -> text "In the expression" $$ (truncateDoc (nest 2 (disp a))))
               locs

instance Error Err where
  strMsg msg = Err [] (text msg)


rethrowWith msg' (Err ps msg) = throwError $ Err ps (msg $$ msg')


-- Like takeWhile, but includes one more element.
takeWhile1 :: (a->Bool) -> [a] -> [a]
takeWhile1 p [] = []
takeWhile1 p (x:xs) | p x       = x : takeWhile1 p xs
                    | otherwise = [x]


-- Very long files are hard to handle in Emacs, etc.
truncateDoc :: Doc -> Doc
truncateDoc doc = 
  if (length rendered < maxlength)
    then doc
    else text $ take maxlength rendered ++ "<EXCESSIVELY LONG OUTPUT TRUNCATED HERE>"
 where rendered = render doc
       maxlength = 10000
