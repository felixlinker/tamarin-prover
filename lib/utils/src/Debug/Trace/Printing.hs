module Debug.Trace.Printing
  ( dbgWith
  , dbg ) where

import Debug.Trace (trace)

dbgWith :: Show b => (a -> b) -> String -> a -> a
dbgWith f msg a = trace (msg ++ " " ++ show (f a)) a

dbg :: Show a => String -> a -> a
dbg = dbgWith id
