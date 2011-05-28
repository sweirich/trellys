{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances, GADTs, TypeOperators, TypeFamilies, RankNTypes #-}
module Language.SepPP.Eval where

import Generics.RepLib
import Unbound.LocallyNameless
import Control.Monad((>=>))
import Control.Monad.Trans
import Control.Applicative
import Control.Monad


-- | We keep two pairs of lists for the ZDown constructor. One represents the
-- children to the left of the current focus. This list is kept in reversed
-- order. The second represents the current focused child, tupled with the
-- children to the right, in standard order.  We carry 'MTup' around to ensure
-- that we have the 'Rep' constraint on all of the elements of the child
-- lists. ZDown also contains a constructor function that takes in as arguments
-- the two lists, and an 'up' continuation.
data Zipper root where
  ZTop :: Rep root => root -> Zipper root
  ZDown :: -- forall r consumed pending hole root.
        (consumed -> pending -> hole) ->
        MTup r consumed -> consumed -> -- Left children
        MTup r pending ->  pending -> -- Focus :*: right children
        (hole -> Zipper root) -> -- continuation for up movements
        Zipper root


-- | 'left' and 'right' movements shuffle the list around, along with adjusting
-- the constructor function. Doing lots of left-right movements will compose a
-- bunch of functions that simply shift the input lists around. It may be wiser
-- to wrap this function in a GADT that indicates what sort of movement has been
-- taken, in which case we can eliminate the composition of inverse movements
-- (e.g.a right movement followed by a left movement) at the time that the
-- second movement is applied, rather than when the constructor is applied.
left :: forall root . Zipper root -> Maybe (Zipper root)
left (ZTop _) = Nothing
left (ZDown f MNil consumed _ _ _) = Nothing
left (ZDown f (xRep :+: xsRep) (x :*: xs) ysRep ys parent) =
  let f' consumed (x :*: pending) = f (x :*: consumed) pending
  in  Just (ZDown f' xsRep xs (xRep :+: ysRep) (x :*: ys) parent)


right :: forall  root . Zipper root -> Maybe (Zipper root)
right (ZTop _) = Nothing
right (ZDown f _ _ MNil pending _) = Nothing
right (ZDown f xsRep xs (yRep :+: ysRep) (y :*: ys) parent) =
  let f' (x :*: consumed) pending = f consumed (x :*: pending)
  in Just (ZDown f' (yRep :+: xsRep) (y :*: xs) ysRep ys parent)


-- | The 'up' movement applies the constructor function followed by the up
-- (parent) continuation.
up :: Zipper root -> Maybe (Zipper root)
up (ZDown f _ consumed _ pending parent) = Just $ parent (f consumed pending)
up z@(ZTop _) = Nothing


-- | The 'down' movement upacks the current focus. In the event that it's a
-- value of a data type, it will then create a ZDown cursor, with the parent
-- continuation replacing the current focus with the (possibly modified) new
-- value. The default focus when moving down will be the leftmost child of the
-- value.
-- If the current focus is /not/ a value of a data type, then we don't move down.
down :: forall root. Zipper root -> Maybe (Zipper root)
down (ZTop (p :: a)) =
  case rep :: R a  of
    (Data dt cons) ->
      case findCon cons p of
        (Val emb tup l) ->
          let c' :: Zipper root
              c' = ZDown (\cons pend -> to emb pend) MNil Nil tup l ZTop
          in Just c'
    _ -> Nothing

down (ZDown f consRep consumed MNil pend parent) = Nothing
down c@(ZDown f consRep consumed (pr :+: prs) ((p :: a) :*: ps) parent) =
  case rep :: R a  of
    (Data dt cons) ->
      case findCon cons p of
        (Val emb tup l) ->
          let c' :: Zipper root
              c' = ZDown (\cons pend -> to emb pend) MNil Nil tup l k
              k x = ZDown f consRep consumed (pr :+: prs) (x :*: ps) parent
          in Just c'

-- | The 'get' function returns the current focus, assuming that there is a
-- current focus. It does a replib 'cast' to do this, so it's necessary for the
-- caller to provide the appropriate context for the cast overloading to be resolved.
get :: forall root a. Rep a => Zipper root -> Maybe a
get (ZDown _ _ _ (_ :+: _) (x :*: _) _) = cast x
get (ZTop a) = cast a
get _ = Nothing


query :: forall root b.  (forall a. Rep a => a -> Maybe b) -> Zipper root -> Maybe b
query f (ZTop x) = f x
query f (ZDown _ _ _ (_ :+: _) (x :*: _) _) = f x
query _ _ = Nothing

-- | The 'put' function replaces the current focus with the supplied value.
put :: Rep a => a -> Zipper root -> Maybe (Zipper root)
put x (ZDown f cRep c (pR :+: psR) (_ :*: ps) parent) = do
  v <- cast x
  return (ZDown f cRep c (pR :+: psR) (v :*: ps) parent)
put x (ZTop _) = do
  x' <- cast x
  return (ZTop x')



-- * Testing
data Term = Lam (Bind (Name Term) Term)
          | App Term Term
          | Var (Name Term) deriving (Show)

$(derive [''Term])

instance Alpha Term
instance Subst Term Term where
  isvar (Var n) = Just $ SubstName n
  isvar _ = Nothing



-- Example terms.

ia = App i
i = (Lam (bind x (Var x)))
  where x = s2n "x"

ja = App j
j = (Lam (bind y (Var y)))
  where y = s2n "y"


oa = App o
o = Lam (bind x (App (Var x) (Var x)))
  where x = s2n "x"
sv = Var (s2n "z")



type Mon a = FreshMT IO a


class Reducible t where
  -- | Perform a reduction. Return Nothing if this is not a redex.
  reduce :: t -> Maybe (Mon t)
  -- | Decompose a term; return the series of movements to get to the subterm of
  -- focus.
  decomp :: t -> Zipper t -> Maybe (Zipper t)

  -- | Deterimine if a form is a value.
  isValue :: t -> Bool


instance Reducible Term where
  reduce (App (Lam binding) t)
    | isValue t = Just $ do
                    (x,body) <- unbind binding
                    return $ subst x t body
    | otherwise = Nothing
  reduce _ = Nothing

  decomp (App t t')
         | not (isValue t) = Just -- current focus (t)
         | not (isValue t') = right -- move right
         | otherwise = const Nothing -- can't decompose.
  decomp _ = const Nothing

  isValue (Var x) = True
  isValue (Lam _) = True
  isValue _ = False


eval t = runFreshMT $ reduction $ Just $ ZTop t

reduction :: Maybe (Zipper Term) -> Mon Term
reduction Nothing = fail "No context"
reduction (Just context)
  | ZTop t <- context, isValue t = return t
  | otherwise =  case get context of
                   Nothing -> fail "No term in the context."
                   Just t -> do
                     case reduce t of
                       Just m -> do
                               t' <- m
                               liftIO $ putStrLn (show t ++ "  -->   " ++ show t')
                               reduction (put t' context)
                       Nothing -> case down context >>= decomp t of
                                    Just c' -> reduction (Just c')
                                    Nothing
                                      | isValue t -> reduction (up context)
                                      | otherwise -> do
                                      liftIO $ putStrLn "Plugging in a non-value. This might not work out at all."
                                      liftIO $ print t
                                      reduction (up context)



-- An editor
-- edit :: Term -> Mon Term
edit t = runFreshMT $ loop (Just (ZTop t))
  where loop :: Maybe (Zipper t) -> Mon (Zipper t)
        loop cxt@(Just c) = do
          cmd <- liftIO getLine
          case lookup cmd list of
            Just m -> m c >>= (\c' -> loop (c' `mplus` cxt))
            Nothing -> loop (Just c)
        list :: [(String,Zipper t -> Mon (Maybe (Zipper t)))]
        list = [("get", \c -> case get c of
                                Just (f :: Term) -> liftIO (print f) >> return (Just c)
                                Nothing -> (liftIO $ putStrLn "Notaterm") >> return (Just c))
               ,("type", getType)
               ,("down", \c -> return (down c))
               ,("up", \c -> return (up c))
               ,("right", \c -> return (right c))
               ,("left", \c -> return (left c))
               ,("unbind", \c -> let (f :: Maybe (Bind (Name Term) Term)) = get c in return (Just c)) ]

        getType :: forall t. Zipper t-> Mon (Maybe (Zipper t))
        getType ctx = case query ty ctx of
                        Just m -> m >> return Nothing
                        Nothing -> return Nothing
         where ty :: forall a. Rep a => a -> Maybe (Mon ())
               ty (x :: a) = Just (liftIO (print (show (rep :: R a))))

        unBind :: forall t. Zipper t -> Mon (Maybe (Zipper t))
        unBind ctx = let mon = query (\t -> unbind' <$> cast t) ctx
                     in case mon of
                          Just m -> return Nothing
                          Nothing -> return Nothing
          where unbind' :: Bind (Name Term) Term -> Mon (Name Term, Term)
                unbind' t = unbind t



