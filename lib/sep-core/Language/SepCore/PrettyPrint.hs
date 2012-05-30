{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances, UndecidableInstances, PackageImports #-}
-- I use Garrin's file as a template.
module Language.SepCore.PrettyPrint where
import Unbound.LocallyNameless hiding (empty,Val,Con,Refl,Equal)
import Text.PrettyPrint
import Control.Applicative hiding (empty)
import "mtl" Control.Monad.Reader
import qualified Data.Set as S

class Disp d where
  disp :: d -> Doc

instance Disp Doc where
  disp = id

instance Disp String where
  disp  = text

instance Disp Int where
  disp = integer . toInteger


instance Rep a => Disp (Name a) where
  disp = cleverDisp


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

-- This function tries to pretty-print terms using the lowest number in
-- the names of the variable (i.e. as close to what the user originally
-- wrote.)
-- It first freshens the free variables of the argument (using the lowest
-- numbers that it can) then displays the term, swapping the free variables
-- with their new name in the process

cleverDisp :: (Display d, Alpha d) => d -> Doc
cleverDisp d =
  runReader (runFreshMT dm) initDI where
    dm = let vars = S.elems (fvAny d)  in
         lfreshen vars $ \vars'  p ->
           (display (swaps p d))

class (Alpha t) => Display t where
  display :: t -> M Doc
  precedence :: t -> Int
  precedence _ = 0

-- 1. Display is monadic :: a -> M Doc
-- 2. Disp is pure :: a -> Doc

-- display :: Disp a => a -> IO Doc
-- display d = runFreshMT $ runReaderT (disp d) 0
instance Rep a => Display (Name a) where
  display = return . text . name2String



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



        


