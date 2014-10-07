{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Language.Trellys.TestReduction where

import Language.Trellys.Syntax

import Language.Trellys.PrettyPrint(Disp(..))
import Language.Trellys.OpSem (cbvStep, erase)
import Language.Trellys.AOpSem (astep)

import Language.Trellys.Environment
import Language.Trellys.Error
import Language.Trellys.TypeMonad

import Text.PrettyPrint.HughesPJ

import Control.Applicative ((<$>))
import Control.Monad.Reader hiding (join)
import Control.Arrow ((&&&), Kleisli(..))

import Language.Trellys.GenericBind

------------- Some test code to exercise the annotated reduction semantics ----------

-- step the term until it's stuck.
reductionPath :: (a -> TcMonad (Maybe a)) -> a -> TcMonad [a]
reductionPath step a = do
  ma' <- step a
  case ma' of 
    Nothing -> return [a]
    Just a' ->  (a : ) <$> reductionPath step a'

newtype ReductionPath a = ReductionPath [a]

-- Printing reduction sequences
instance Disp a => Disp (ReductionPath a) where
  disp (ReductionPath path) = foldr (\x y -> x $$ text "--->" $$ y) empty (map disp path)

data AndTheErasureIs = AndTheErasureIs ATerm ETerm

instance Disp AndTheErasureIs where
  disp (a `AndTheErasureIs` t) = 
      disp a $$ parens (text "erased version:" $$ disp t)

testReduction :: ATerm -> TcMonad ()
testReduction a = do
  apath <- reductionPath astep a
  eLastA <- erase (last apath)
  eA <- erase a
  aEpath <- reductionPath cbvStep eA
  let lastEA = last aEpath
  apathAnn <- mapM ((return . uncurry AndTheErasureIs) <=< runKleisli (Kleisli return &&& Kleisli erase)) apath
  unless (eLastA `aeq` lastEA) $ do
    liftIO $ putStrLn "Oops, mismatch between annotated and erased semantics"
    liftIO $ putStrLn $ render (text "Erased reduction path:" $$ disp (ReductionPath aEpath))
    liftIO $ putStrLn $ render (text "Annotated reduction path:" $$ disp (ReductionPath apathAnn))
    err [DS "Something went wrong, see above"]

--Print the reductions
printReductionPath :: ATerm -> TcMonad ()
printReductionPath a = do
  liftIO $ putStrLn $ render (disp a)
  ma' <- astep a
  case ma' of 
    Nothing -> return ()
    Just a' -> do
                 liftIO $ putStrLn "---->"
                 printReductionPath a'
