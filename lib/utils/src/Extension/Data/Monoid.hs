{-# LANGUAGE CPP #-}
-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
module Extension.Data.Monoid (
    module Data.Monoid

  , MinMaxMap(..)
  , minMaxMapSingleton
  ) where

import qualified Data.Map as M
import Data.Monoid

newtype MinMaxMap k a = MinMaxMap { getMinMaxMap :: M.Map k (a, a) }

minMaxMapSingleton :: Ord k => k -> a -> MinMaxMap k a
minMaxMapSingleton k v = MinMaxMap $ M.singleton k (v, v)

instance (Ord k, Ord a) => Semigroup (MinMaxMap k a) where
  (MinMaxMap m1) <> (MinMaxMap m2) = MinMaxMap $ M.unionWith (\(min1, max1) (min2, max2) -> (min min1 min2, max max1 max2)) m1 m2

instance (Ord k, Ord a) => Monoid (MinMaxMap k a) where
  mempty = MinMaxMap M.empty
  mappend = (<>)
