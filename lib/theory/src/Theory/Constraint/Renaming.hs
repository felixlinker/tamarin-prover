{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE ViewPatterns #-}
module Theory.Constraint.Renaming
  ( applyRenaming
  , renamedTimePoints
  , Renaming
  , giSubst
  , idRenaming
  , noRenaming
  , Renamable(..)
  , mapVar
  , mapVarM
  , (~><~)
  , MaybeMaude
  , MaybeRenaming
  ) where

import Data.Label as L ( get, mkLabels )
import qualified Data.Map as M
import qualified Data.Set as S
import Term.LTerm (Term (LIT), Lit (Var), IsVar, IsConst, LVar(..), LSort(..), VTerm, Name, HasFrees, freesList, LNTerm(..))
import Control.Monad (guard, MonadPlus (mzero))
import Extension.Data.Label (modA)
import Theory.Model.Rule (RuleACInst, getRuleRenaming)
import Term.Unification (Apply (apply), SubstVFresh(..), WithMaude, LNSubstVFresh, LNSubst, Subst(..), emptySubst)
import Control.Monad.Trans.Maybe (MaybeT(..), mapMaybeT)
import GHC.Generics (Generic)
import Data.Binary
import Control.DeepSeq
import Theory.Model.Fact (LNFact, unifyLNFacts)
import Data.Maybe (fromJust, mapMaybe, listToMaybe)
import Theory.Constraint.System.Constraints (Goal(..))

-- A Renaming is a substitution that always maps to variables.
newtype Renaming s = Renaming
  { _giSubst  :: s }
  deriving ( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''Renaming])

termToVar :: VTerm Name LVar -> Maybe LVar
termToVar (LIT (Var v)) = Just v
termToVar _             = Nothing

renamedTimePoints :: Renaming LNSubst -> [(LVar, LVar)]
renamedTimePoints r =
  let subst = sMap $ L.get giSubst r
      timepoints = filter ((== LSortNode) . lvarSort) $ M.keys subst
  in zip timepoints (map (fromJust . termToVar . (subst M.!)) timepoints)

fromUnification :: HasFrees a => a -> a -> LNSubstVFresh -> Maybe (Renaming LNSubst)
fromUnification a1 a2 = fmap (Renaming . Subst . M.map (LIT . Var) . selfCompose) . M.foldrWithKey canonicalize (Just M.empty) . svMap
  where
    rng1 = range a1
    rng2 = range a2

    canonicalize :: LVar -> VTerm Name LVar -> Maybe (M.Map LVar LVar) -> Maybe (M.Map LVar LVar)
    canonicalize v (termToVar -> mtv) macc = do
      tv <- mtv
      aux tv <$> macc
      where
        aux tv
          | v `S.member` rng1 = M.insert v tv
          | v `S.member` rng2 = M.insert tv v
          | otherwise = error "illegal state"

    -- @selfCompose@ handles cases such as the following. Presume we want to
    -- rename variable x to variable y. One unifier could be [x->z, y->z].
    -- @canonicalize@ above will store this as [x->z,z->y] and @selfCompose@
    -- eliminates z.
    selfCompose :: M.Map LVar LVar -> M.Map LVar LVar
    -- @<> m@ keeps mappings that are already correct.
    selfCompose m = M.filterWithKey (\k _ -> k `S.member` rng1) (M.compose m m <> m)

    range :: HasFrees a => a -> S.Set LVar
    range = S.fromList . freesList

applyRenaming :: Apply s a => Renaming s -> a -> a
applyRenaming (Renaming s) = apply s

idRenaming :: MaybeRenaming (Subst c v)
idRenaming = MaybeT $ return $ Just $ Renaming emptySubst

noRenaming :: MaybeRenaming s
noRenaming = mzero

mapVar :: (IsConst c, IsVar v) => v -> v -> Renaming (Subst c v) -> Maybe (Renaming (Subst c v))
mapVar from to = if from == to then Just else modA giSubst modLnSubst
  where
    tryInsert :: (Ord k, Eq v) => k -> v -> Maybe (M.Map k v) -> Maybe (M.Map k v)
    tryInsert k v maybeMap = do
      m <- maybeMap
      guard (M.findWithDefault v k m == v)
      return $ M.insert k v m

    modLnSubst (Subst m) = Subst <$> tryInsert from (LIT $ Var to) (Just m)

mapVarM :: (IsConst c, IsVar v) => v -> v -> MaybeRenaming (Subst c v) -> MaybeRenaming (Subst c v)
mapVarM v1 v2 = mapMaybeT (\mm -> do
  renaming <- mm
  return $ mapVar v1 v2 =<< renaming)

type MaybeMaude t = MaybeT WithMaude t

type MaybeRenaming s = MaybeMaude (Renaming s)

class Renamable t s where
  -- |  Compute a renaming from the first argument to the second. The renaming
  --    should ensure that whenever @Apply s t@, then @applyRenaming (t1 ~> t2) t1@
  --    is contained in @t2@.
  (~>) :: t -> t -> MaybeRenaming s

instance Renamable RuleACInst LNSubst where
  r1 ~> r2 = MaybeT $ (fromUnification r1 r2 =<<) <$> getRuleRenaming r1 r2

(~><~) :: (IsConst c, IsVar v) => MaybeRenaming (Subst c v) -> MaybeRenaming (Subst c v) -> MaybeRenaming (Subst c v)
(~><~) lrm rrm = do
  (Renaming lsubst) <- lrm
  (Renaming rsubst) <- rrm
  MaybeT $ return $ Renaming <$> merge lsubst rsubst
  where
    merge :: (IsConst c, IsVar v) => Subst c v -> Subst c v -> Maybe (Subst c v)
    merge (Subst m1) (Subst m2) = Subst <$> mergeMaps m1 m2

instance Renamable LNFact LNSubst where
  fa1 ~> fa2 = MaybeT $ listToMaybe . mapMaybe (fromUnification fa1 fa2) <$> unifyLNFacts fa1 fa2

instance Renamable LVar LNSubst where
  v1 ~> v2 = MaybeT $ return $ Just $ Renaming $ Subst $ M.singleton v1 (LIT $ Var v2)

instance Renamable LNTerm LNSubst where
  LTerm n1 v1 ~> LTerm n2 v2 = mzero

instance Renamable Goal LNSubst where
  (ActionG v1 f1) ~> (ActionG v2 f2) = mapVarM v1 v2 (f1 ~> f2)
  (ChainG (c1, _) (p1, _)) ~> (ChainG (c2, _) (p2, _)) = (c1 ~> c2) ~><~ (p1 ~> p2)
  (PremiseG (p1, _) f1) ~> (PremiseG (p2, _) f2) = (p1 ~> p2) ~><~ (f1 ~> f2)
  (SplitG _) ~> (SplitG _) = idRenaming
  (DisjG _) ~> (DisjG _) = mzero
  (SubtermG (ft1, st1)) ~> (SubtermG (ft2, st2)) = ft1 ~> ft2
  (Weaken _) ~> (Weaken _) = mzero
  (Cut _) ~> (Cut _) = mzero
  _ ~> _ = mzero

instance (IsConst c, IsVar v, Renamable d (Subst c v)) => Renamable [d] (Subst c v) where
  l1 ~> l2 = foldl (~><~) idRenaming $ zipWith (~>) l1 l2

mergeMaps :: (Ord k, Eq v) => M.Map k v -> M.Map k v -> Maybe (M.Map k v)
mergeMaps m1 m2 = M.fromAscList <$> go (M.toAscList m1) (M.toAscList m2)
  where
    go :: (Ord a, Eq b) => [(a, b)] -> [(a, b)] -> Maybe [(a, b)]
    go [] l2 = Just l2
    go l1 [] = Just l1
    go l1@((k1, v1):t1) l2@((k2, v2):t2)
      | k1 == k2 && v1 == v2 = ((k1,v1):) <$> go t1 t2
      | k1 < k2 = ((k1, v1):) <$> go t1 l2
      | k2 < k1 = ((k2, v2):) <$> go l1 t2
      | otherwise = Nothing
