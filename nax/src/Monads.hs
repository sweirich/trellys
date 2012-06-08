{-# LANGUAGE DeriveFunctor #-}
module Monads where

import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO(fixIO,hClose,hFlush,stdout)
-- import qualified System.IO.Error as Err -- Deprecated
import qualified Control.Exception         -- Use this instead
import System.IO.Unsafe(unsafePerformIO)
import Text.Parsec.Pos(SourcePos,newPos)
import Control.Monad (filterM,liftM)
import Control.Applicative ((<$>))

import Names(SourcePos,noPos)

tryIO :: IO a -> IO (Either IOError a)
tryIO = Control.Exception.try
--------------------------------------
-- Monads for computing values
-- Note that values include delayed computations 
-- which are FIO computations

-- This should really be an 'Either Fail x': the error handling code
-- wants to deal with the exception, not the 'Ok'.
data Exception x
   = Ok x
   | Fail { srcPos  :: SourcePos  -- Source Location of Error
          , msg     :: String     -- message
          }
  deriving (Functor)
showFail (Fail srcPos msg) =  show srcPos ++ ": " ++ msg

instance Monad Exception where
  return x = Ok x
  (>>=) (Ok x) f = f x
  -- Interesting: we have to rebuild the 'Fail' to change its type.
  -- The following code, which does not depend on the structure of
  -- 'Fail', will not work:
  --
  -- (>>=) fail'@(Fail {}) _  = fail'
  (>>=) (Fail srcPos msg) _  = Fail srcPos msg
  fail msg = Fail noPos msg

--------------------------------------------
-- FIO  = IO with catchable failure
--
-- Aproximately 'ErrorT e IO x', for 'e' some error type corresponding
-- to 'Fail'.

newtype FIO x = FIO(IO (Exception x))
unFIO (FIO x) = x

instance Monad FIO where
  fail s = FIO(return(Fail noPos s))
  return x = FIO(return(Ok x))
  (>>=) (FIO a) g = FIO w
    where w = do { x <- a
                 ; case x of
                    Ok z -> unFIO(g z)
                    Fail loc s -> return(Fail loc s)}

instance Functor FIO where
  fmap f (FIO x) = FIO(fmap (fmap f) x)

-- | This is usually called 'catch'.  The standard 'handle' has the
-- arguments reversed.
handle :: FIO a -> (Exception a -> FIO a) -> FIO a
handle (FIO comp) handler = FIO r
 where
  r = do
    a <- comp
    case a of
      Fail _ _ -> unFIO $ handler a
      Ok _     -> return a

-- | On error, apply the transformer to the error msg
handleM :: FIO a -> (String -> String) -> FIO a
handleM comp transformer = comp `handle` handler
  where handler f@(Fail { msg = oldMsg }) = 
          FIO . return $ f { msg = transformer oldMsg }

runFIO :: FIO x -> IO x
runFIO (FIO mx) = do
  ex <- mx
  case ex of
    Ok x    -> return x
    Fail {} -> error . showFail $ ex

-- for testing only
instance Show a => Show (FIO a) where
  show x = show (unsafePerformIO(runFIO x))

fio :: IO x -> FIO x
fio x = FIO $ do result <- tryIO x 
                 case result of
                   Left err  -> return (Fail noPos ("\n"++show err))
                   Right ans -> return (Ok ans)

write = fio . putStr
writeln = fio . putStrLn
nextInteger = do { n <- readIORef counter; writeIORef counter (n+1); return n }
next = fio nextInteger

fresh = unique "_x"
unique s = do { n <- next; return (s++show n)}

-- ???: why unsafePerformIO ?
counter :: IORef Integer
counter = unsafePerformIO(newIORef 0)

newRef x = fio(newIORef x)
readRef r = fio(readIORef r)
writeRef x r = fio(writeIORef x r)

-----------------------------------------------

anyM :: Monad m => (b -> m Bool) -> [b] -> m Bool
anyM p xs = or `liftM` mapM p xs

unionByM :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m [a]
unionByM eqM xs ys = (xs ++) `liftM` filterM notElemXsM ys
 where notElemXsM y = not `liftM` anyM (eqM y) xs
