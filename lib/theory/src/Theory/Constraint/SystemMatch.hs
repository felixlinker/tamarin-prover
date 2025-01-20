{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
module Theory.Constraint.SystemMatch
  ( SystemMatch(..)
  , runSystemMatch
  , graphDomain
  , extendWith
  , Matchable(..)
  , AFGoals(..)
  , mapNode
  , singleton
  ) where

import qualified Data.Map as M
import qualified Data.Set as S

import Term.LTerm
import Control.Monad (guard)
import Theory.Model.Rule (RuleACInst, getRuleName, Rule (Rule))
import Term.Unification
import Theory.Model.Fact (LNFact, Fact (factTag, factTerms))
import Data.Maybe (mapMaybe, fromMaybe)
import Theory.Constraint.System.Constraints (Goal(..))
import Utils.Misc (zipWithStrictLeft, peak, mergeDisjoint)
import Data.List (permutations)

singleton :: LVar -> LNTerm -> LNSubst
singleton v t = Subst $ M.singleton v t

data SystemMatch = NoSystemMatch | SystemMatch
  { graphMatch :: M.Map NodeId NodeId
  , graphImage :: S.Set LVar
  , matchProblem :: Match LNTerm }
  deriving Eq

fromMatching :: Match LNTerm -> SystemMatch
fromMatching = SystemMatch M.empty S.empty

graphDomain :: SystemMatch -> S.Set LVar
graphDomain NoSystemMatch = S.empty
graphDomain (SystemMatch nids _ _) = M.keysSet nids

runSystemMatch :: MaudeHandle -> SystemMatch -> Maybe LNSubst
runSystemMatch _ NoSystemMatch = Nothing
runSystemMatch mh (SystemMatch nids _ matching) =
  peak $ mapMaybe (mergeSubsts (Subst $ fmap varTerm nids)) (runMatchLNTerm mh matching)

instance Semigroup SystemMatch where
  NoSystemMatch <> _ = NoSystemMatch
  _ <> NoSystemMatch = NoSystemMatch
  (SystemMatch nidM1 nidD1 match1) <> (SystemMatch nidM2 nidD2 match2) =
    fromMaybe NoSystemMatch $ do
      nidM <- mergeDisjoint nidM1 nidM2
      return $ SystemMatch nidM (nidD1 <> nidD2) (match1 <> match2)

instance Monoid SystemMatch where
  mempty = SystemMatch M.empty S.empty (DelayedMatches [])

extendWith :: Functor f => SystemMatch -> [f SystemMatch] -> [f SystemMatch]
extendWith NoSystemMatch _ = []
extendWith pr l = map (fmap (pr <>)) l

mapNode :: NodeId -> NodeId -> SystemMatch -> SystemMatch
mapNode _ _ NoSystemMatch = NoSystemMatch
mapNode from to r@(SystemMatch m i _)
  -- | If to is already in the image, it must be mapped by the same variable.
  --   Otherwise, this will not be a match.
  | to `S.member` i = fromMaybe NoSystemMatch $ do
    to' <- M.lookup from m
    guard (to == to')
    return r
  -- | If @from@ is already mapped, we cannot extend this matching. It cannot
  --   map to @to@ either because this would have been caught by the previous
  --   guard.
  | M.member from m = NoSystemMatch
  | otherwise = r { graphMatch = M.insert from to m, graphImage = S.insert to i }

class Matchable t where
  -- |  Compute a matching from the first argument to the second. The matching
  --    should ensure that whenever @Apply LNSubst t@, then
  --    @apply (runSystemMatch mh (t1 ~> t2)) t1 == t2@.
  (~>) :: t -> t -> SystemMatch

instance Matchable a => Matchable (Maybe a) where
  Nothing ~> Nothing = mempty
  _ ~> Nothing = NoSystemMatch
  Nothing ~> _ = NoSystemMatch
  Just a1 ~> Just a2 = a1 ~> a2

instance (Matchable a, Matchable b) => Matchable (Either a b) where
  Left a1 ~> Left a2 = a1 ~> a2
  Right b1 ~> Right b2 = b1 ~> b2
  _ ~> _ = NoSystemMatch

instance Matchable RuleACInst where
  r1@(Rule _ ps1 cs1 as1 _) ~> r2@(Rule _ ps2 cs2 as2 _)
    | getRuleName r1 /= getRuleName r2 = NoSystemMatch
    | otherwise = mconcat $ zipWith (~>) (ps1 ++ cs1 ++ as1) (ps2 ++ cs2 ++ as2)

instance Matchable LNFact where
  fa1 ~> fa2 
    | factTag fa1 /= factTag fa2 = NoSystemMatch
    | otherwise = fromMatching $ mconcat $ zipWith matchWith (factTerms fa2) (factTerms fa1)

-- | A list of action fact from action fact goals that share the same timepoint.
newtype AFGoals = AFGoals { afgs :: [LNFact] } deriving (Eq, Ord, Show)

-- |  This instance is very inefficient (because it calls permutations), but it
--    will in all likelihood only be called on very small lists.
instance Matchable AFGoals where
  (AFGoals fs1) ~> (AFGoals fs2) = fromMaybe NoSystemMatch $ matchFacts fs1 fs2
    where
      tryPermutation :: [LNFact] -> [LNFact] -> Maybe SystemMatch
      tryPermutation smaller larger = do
        r <- mconcat <$> zipWithStrictLeft (~>) smaller larger
        guard (NoSystemMatch /= r)
        return r

      matchFacts :: [LNFact] -> [LNFact] -> Maybe SystemMatch
      matchFacts smaller larger = peak $ mapMaybe (`tryPermutation` larger) (permutations smaller)

instance Matchable LVar where
  v1 ~> v2
    | lvarSort v1 /= lvarSort v2 = NoSystemMatch
    | v1 == v2 = mempty
    | otherwise = mapNode v1 v2 mempty

instance Matchable LNTerm where
  (LIT (Var v)) ~> (LIT (Var w)) = v ~> w
  (LIT (Con x)) ~> (LIT (Con y))
    | x == y = mempty
    | otherwise = NoSystemMatch
  (LIT _) ~> (LIT _) = NoSystemMatch
  t1 ~> t2 = fromMatching (matchWith t2 t1)

instance Matchable Goal where
  (ActionG v1 f1) ~> (ActionG v2 f2) = mapNode v1 v2 (f1 ~> f2)
  (ChainG (c1, _) (p1, _)) ~> (ChainG (c2, _) (p2, _)) = (c1 ~> c2) <> (p1 ~> p2)
  (PremiseG (p1, _) f1) ~> (PremiseG (p2, _) f2) = (p1 ~> p2) <> (f1 ~> f2)
  (SplitG _) ~> (SplitG _) = mempty
  (DisjG _) ~> (DisjG _) = mempty
  (SubtermG (ft1, st1)) ~> (SubtermG (ft2, st2)) = (ft1 ~> ft2) <> (st1 ~> st2)
  (Weaken _) ~> (Weaken _) = mempty
  (Cut _) ~> (Cut _) = mempty
  _ ~> _ = NoSystemMatch
