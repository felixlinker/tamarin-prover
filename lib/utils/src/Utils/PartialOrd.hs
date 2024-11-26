{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Utils.PartialOrd (
    PartialOrdering(..)
  , PartialOrder(..)
  , TopoSortedOrder
  , toList
  , toposort
  , TransClosedOrder(..)
  , domain
  , image
  , universe
  , unionDisjoint
  , minima
  , getGreatest
  , isSmaller
  , isLarger
  , getLarger
  , getDirectlyLarger
  , fromTopoSorted
  , fromSet
  , toRelation ) where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad (guard)
import Control.Applicative ((<|>))
import Data.Maybe (fromMaybe)
import Data.List (uncons, groupBy)
import Utils.Two

data PartialOrdering = PLT | PEQ | PGT | PINCOMP deriving (Eq, Show)

-- |This class implements a partial order. Elements of type @a@ can be compared
--  using @pcomp@. The datastructure of type @t@ stores the partial order
--  relation. The partial order is assumed to be reflexive using the @Eq@
--  instance on type @a@.
class PartialOrder t a where
  -- |Compare two elements. @pcomp a a'@ checks the relation from @a@ to @a'@,
  --  e.g., if it returns @PLT@ this means that a < a'.
  pcomp :: t a -> a -> a -> PartialOrdering
  -- |Add an element to the partial order relation. @pinsert (a, a')@ adds
  --  a < a' to the relation.
  pinsert :: (a, a) -> t a -> t a
  -- |The empty but reflexive relation.
  pempty :: t a

-- |This instance implements left-to-right, transitive concatenation of partial
--  order relations. For example, if we have a < b < c, then
--  @(pcomp a b) <> (pcomp b c)@ yields PLT because transitively, a < c.
instance Semigroup PartialOrdering where
  PINCOMP <> _ = PINCOMP
  _ <> PINCOMP = PINCOMP
  PLT <> PGT = PINCOMP
  PGT <> PLT = PINCOMP
  PLT <> PLT = PLT
  PGT <> PGT = PGT
  PEQ <> po = po
  po <> PEQ = po

-- |A partial order implemented using an ascending, topologically sorted list.
newtype TopoSortedOrder a = TopoSortedOrder [(a, a)] deriving Show

toList :: TopoSortedOrder a -> [(a, a)]
toList (TopoSortedOrder l) = l

tcons :: (a, a) -> TopoSortedOrder a -> TopoSortedOrder a
tcons a (TopoSortedOrder l) = TopoSortedOrder (a:l)

-- |Topologically sort a list of partial order relations. Returns @Nothing@ if
--  the relation is cyclic.
toposort :: Ord a => S.Set (a, a) -> Maybe (TopoSortedOrder a)
toposort = fmap TopoSortedOrder . go
  where
    go :: Ord a => S.Set (a, a) -> Maybe [(a, a)]
    go s  | S.null s  = Just []
          | otherwise =
            let noOutgoing = S.map fst s S.\\ S.map snd s
                (mins, rest) = S.partition ((`S.member` noOutgoing) . fst) s
            in  if   S.null mins
                then Nothing
                else (S.toList mins ++) <$> go rest

instance Eq a => PartialOrder TopoSortedOrder a where
  pcomp (TopoSortedOrder l) = go l
    where
      go :: Eq a => [(a, a)] -> a -> a -> PartialOrdering
      go [] a b
        | a == b = PEQ
        | otherwise = PINCOMP
      go ((x,y):t) a b
        | a == b = PEQ
        | x == a = PLT <> go t y b
        | x == b = PGT <> go t a y
        | otherwise = go t a b

  pinsert a (TopoSortedOrder []) = TopoSortedOrder [a]
  pinsert a@(_, agt) (TopoSortedOrder l@(h@(hlt, _):t))
    | agt == hlt = TopoSortedOrder (a:l)
    | otherwise = tcons h $ pinsert a (TopoSortedOrder t)

  pempty = TopoSortedOrder []

-- |Transitively closed, partial order. The domain of the order is implicit.
data TransClosedOrder a = TransClosedOrder
  { raw :: M.Map a (S.Set a)
  -- ^The relation elements without the transitive closure.
  , toGreater :: M.Map a (S.Set a)
  -- ^Map that maps elements to larger elements.
  , maxima :: S.Set a
  -- ^All maxima of the partial order, i.e., all elements that are contained in
  --  no key of @ltMap@.
  } deriving( Show, Eq, Ord, Generic, NFData, Binary )

domain :: Ord a => TransClosedOrder a -> S.Set a
domain = M.keysSet . raw

image :: Ord a => TransClosedOrder a -> S.Set a
image = mconcat . M.elems . raw

universe :: Ord a => TransClosedOrder a -> S.Set a
universe ord = domain ord <> maxima ord

minima :: Ord a => TransClosedOrder a -> S.Set a
minima tco = domain tco S.\\ image tco

expand :: M.Map a (S.Set a) -> [(a, a)]
expand = concatMap (\(a, as) -> map (,a) (S.toList as)) . M.toList

-- | Take the union of two orders closed under transitivity assuming that their
--   elements are disjoint. The precondition is not checked.
unionDisjoint :: Ord a => TransClosedOrder a -> TransClosedOrder a -> TransClosedOrder a
unionDisjoint (TransClosedOrder r m maxes) (TransClosedOrder r' m' maxes') =
  TransClosedOrder (r <> r') (m <> m') (maxes <> maxes')

-- |Take the union of two partial orders and compute their transitive closure.
instance Ord a => Semigroup (TransClosedOrder a) where
  order <> TransClosedOrder raw _ _ = foldr pinsert order (expand raw)

-- |Get the greatest element of the partial order. Returns @Nothing@ if the
--  relation is empty or there are multiple maxima.
getGreatest :: TransClosedOrder a -> Maybe a
getGreatest order = do
  (grtst, t) <- uncons $ S.toList $ maxima order
  guard (null t)
  return grtst

isLarger :: Ord a => TransClosedOrder a -> a -> a -> Bool
isLarger ord = flip (isSmaller ord)

isSmaller :: Ord a => TransClosedOrder a -> a -> a -> Bool
isSmaller ord smaller larger = larger `S.member` getLarger ord smaller

-- |Get all values larger than the given one.
getLarger :: Ord a => TransClosedOrder a -> a -> S.Set a
getLarger order a = fromMaybe S.empty (M.lookup a (toGreater order))

-- |Get all values larger than the given one without appealing to transitivity.
getDirectlyLarger :: Ord a => TransClosedOrder a -> a -> S.Set a
getDirectlyLarger (TransClosedOrder raw _ _) a = fromMaybe S.empty (M.lookup a raw)

instance Ord a => PartialOrder TransClosedOrder a where
  pcomp (TransClosedOrder _ m _) a b
    | a == b = PEQ
    | otherwise = fromMaybe PINCOMP $
          (lookupGT b a >> return PLT)
      <|> (lookupGT a b >> return PGT)
    where
      lookupGT x y = do
        yLTx <- S.member y <$> M.lookup x m
        guard yLTx

  pinsert (aLt, aGt) (TransClosedOrder raw m maxima) =
    let raw' = M.alter (Just . maybe (S.singleton aGt) (S.insert aGt)) aLt raw
        m' = M.alter ((Just (S.singleton aGt) <> M.lookup aGt m) <>) aLt m
        maxima' = S.delete aLt (if not (M.member aGt raw) then S.insert aGt maxima else maxima)
    in TransClosedOrder raw' m' maxima'

  pempty = TransClosedOrder M.empty M.empty S.empty

fromTopoSorted :: Ord a => TopoSortedOrder a -> TransClosedOrder a
fromTopoSorted (TopoSortedOrder l) = uncurry (TransClosedOrder (collect l)) (go M.empty S.empty (reverse l))
  where
    collect :: Ord a => [(a, a)] -> M.Map a (S.Set a)
    collect = M.fromList . map (twice (fst . head) (S.fromList . map snd)) . groupBy (\a1 a2 -> fst a1 == fst a2)

    alterF :: Ord a => a -> Maybe (S.Set a) -> Maybe (S.Set a) -> S.Set a
    alterF a s1 s2 = maybe (S.singleton a) (S.insert a) (s1 <> s2)

    go :: Ord a => M.Map a (S.Set a) -> S.Set a -> [(a, a)] -> (M.Map a (S.Set a), S.Set a)
    go gtMap maxima [] = (gtMap, maxima)
    go gtMap maxima ((st,gt):es) =
      let transitivelyGreater = M.lookup gt gtMap
          gtMap' = M.alter (Just . alterF gt transitivelyGreater) st gtMap
          maxima' = if not (M.member gt gtMap) then S.insert gt maxima else maxima
      in go gtMap' maxima' es

fromSet :: Ord a => S.Set (a, a) -> Maybe (TransClosedOrder a)
fromSet = fmap fromTopoSorted . toposort

toRelation :: Ord a => TransClosedOrder a -> S.Set (a, a)
toRelation (TransClosedOrder _ m _) = S.fromList $ expand m
