{-# LANGUAGE TupleSections #-}
module Utils.Two
  ( Two(..)
  , two
  , tuple
  , twice
  , mapTwice ) where

import Data.Bifunctor (bimap)

-- | @Two@ is almost like a tuple but whereas instances of @Functor@, etc., for
-- tuples are defined on the second element always, @Two@ defines it on both.
newtype Two a = Two (a, a)

instance Show a => Show (Two a) where
  show (Two t) = show t

two :: a -> a -> Two a
two a = Two . (a,)

tuple :: Two a -> (a, a)
tuple (Two t) = t

instance Semigroup a => Semigroup (Two a) where
  (Two (x, y)) <> (Two p) = Two (bimap (x <>) (y <>) p)

instance Monoid a => Monoid (Two a) where
  mempty = Two (mempty, mempty)

instance Functor Two where
  fmap f (Two p) = Two (bimap f f p)

instance Applicative Two where
  pure a = Two (a, a)
  (Two (f, g)) <*> (Two p) = Two (bimap f g p)

instance Foldable Two where
  foldr f b (Two t) = foldr f b t

instance Traversable Two where
  traverse f (Two (a1, a2)) = two <$> f a1 <*> f a2

twice :: (a -> b) -> (a -> c) -> a -> (b, c)
twice f g = bimap f g . tuple . pure

mapTwice :: (a -> b) -> (a, a) -> Two b
mapTwice f = fmap f . uncurry two
