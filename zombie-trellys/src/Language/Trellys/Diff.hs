{-# LANGUAGE TupleSections, ViewPatterns #-}
{-# OPTIONS_GHC -Wall  #-}

module Language.Trellys.Diff where 

import Control.Applicative
import Control.Monad

import Language.Trellys.GenericBind
import Language.Trellys.OpSem
import Language.Trellys.Syntax

-- (diff a1 a2) returns a copy of a1 where (AHighlight) has been added around
-- every non-erased subexpression that differs from a2. This is used to print 
-- more readable error messages.
diff :: (Applicative m, Fresh m) => ATerm -> ATerm -> m ATerm 

--Erased head constructors:
diff (ACumul a k) b = ACumul <$> diff a b <*> pure k
diff a (ACumul b _k) = diff a b
diff (AUnbox a) b = AUnbox <$> diff a b
diff a (AUnbox b) = diff a b
diff (ABox a th) b = ABox <$> diff a b <*> pure th
diff a (ABox b _th) = diff a b
diff (AAt a th) (AAt b th') | th==th' = AAt <$> diff a b <*> pure th
diff (AConv a pf) (AConv b _pf) = AConv <$> diff a b <*> pure pf
diff (AHighlight a) b = diff a b
diff a (AHighlight b) = diff a b

--Non-erased head constructors 
diff (AApp ep a1 a2 aTy) (AApp ep' b1 b2 _bTy) | ep==ep'
 = AApp <$> pure ep <*> diff a1 b1 <*> diff a2 b2 <*> pure aTy
diff (ATyEq a1 a2) (ATyEq b1 b2) 
 = ATyEq <$> diff a1 b1 <*> diff a2 b2
diff (ATCon d as) (ATCon d' bs) | d==d' && length as == length bs 
 = ATCon d <$> zipWithM diff as bs
diff (ADCon d th as1 as2) (ADCon d' _th' bs1 bs2) | d==d'  && map snd as2 == map snd bs2
 = ADCon d th <$> zipWithM diff as1 bs1 <*> zipWithM diffFirst as2 bs2
diff (AArrow k ex ep bnd) (AArrow k' ex' ep' bnd') | k==k' && ex==ex' && ep==ep'
 = do
  Just ((x,unembed -> a1), a2, (_,unembed -> b1), b2) <- unbind2 bnd bnd'
  da1 <- diff a1 b1
  da2 <- diff a2 b2
  return $ AArrow k ex ep (bind (x,embed da1) da2)
diff (ALam th ty ep bnd) (ALam _th' _ty' ep' bnd') | ep==ep' = do
  Just (x, a, _, b) <- unbind2 bnd bnd'
  da <- diff a b
  return $ ALam th ty ep (bind x da)
diff (AInd ty ep bnd) (AInd _ty' ep' bnd') | ep==ep' = do
  Just ((x,y), a, (_,_), b) <- unbind2 bnd bnd'
  da <- diff a b
  return $ AInd ty ep (bind (x,y) da)
diff (ARec ty ep bnd) (ARec _ty' ep' bnd') | ep==ep' = do
  Just ((x,y), a, (_,_), b) <- unbind2 bnd bnd'
  da <- diff a b
  return $ ARec ty ep (bind (x,y) da)
diff (ALet Runtime bnd (th,ty)) (ALet Runtime bnd' _) = do
  Just ((x,y,unembed -> a1), a2, (_,_,unembed -> b1), b2) <- unbind2 bnd bnd'
  da1 <- diff a1 b1
  da2 <- diff a2 b2
  return $ ALet Runtime (bind (x,y,embed da1) da2) (th,ty)
diff (ALet Erased bnd (th,ty)) (ALet Erased bnd' _) = do
  Just ((x,y,unembed -> a1), a2, (_,_,_), b2) <- unbind2 bnd bnd'
  da2 <- diff a2 b2
  return $ ALet Erased (bind (x,y,embed a1) da2) (th,ty)
diff (ACase a bnd (th,ty)) (ACase b bnd' _) = do
  Just (x, alts, _, alts') <- unbind2 bnd bnd'
  if map aMatchConstructor alts == map aMatchConstructor alts'
    then do
            da <- diff a b
            dalts <- zipWithM diffMatch alts alts'
            return $ ACase da (bind x (dalts)) (th,ty)
    else 
      return (AHighlight (ACase a bnd (th,ty)))

-- The rest
diff a b = do
 ea <- erase a
 eb <- erase b
 if (ea `aeq` eb)
   then return a
   else return (AHighlight a)

diffFirst :: (Applicative m,Monad m, Fresh m) => 
             (ATerm,Epsilon) -> (ATerm,Epsilon) -> m (ATerm,Epsilon)
diffFirst (a,ep) (b,ep') | ep==ep' = (,ep) <$> diff a b
diffFirst _ _ = error "diffFirst call on pairs with unequal second component"

diffMatch :: (Applicative m, Monad m, Fresh m) =>
             AMatch -> AMatch -> m AMatch
diffMatch (AMatch d bnd) (AMatch d' bnd') | d==d' = do
  Just (xs, a, _, b) <- unbind2 bnd bnd'
  da <- diff a b
  return $ AMatch d (bind xs da)
diffMatch _ _ = error "diffMatch called on branches with unequal constructors"

