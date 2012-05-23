module UniqInteger(nextinteger,resetnext) where

import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)

----------------------------
-- unique integer supply

nextinteger = do { n <- readIORef counter; writeIORef counter (n+1); return n }
resetnext m = writeIORef counter m

counter :: IORef Integer
counter = unsafePerformIO(newIORef 10)
