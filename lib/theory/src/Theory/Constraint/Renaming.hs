{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DeriveAnyClass  #-}
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
import Term.LTerm (Term (LIT), Lit (Var), IsVar, IsConst, LVar(..), LSort(..), VTerm, Name, varOccurences)
import Control.Monad (guard, MonadPlus (mzero))
import Extension.Data.Label (modA)
import Theory.Model.Rule (RuleACInst, getRuleRenaming)
import Term.Unification (Apply (apply), SubstVFresh(..), WithMaude, LNSubstVFresh, LNSubst, Subst(..), emptySubst)
import Control.Monad.Trans.Maybe (MaybeT(..), mapMaybeT)
import GHC.Generics (Generic)
import Data.Binary
import Control.DeepSeq

newtype Renaming s = Renaming
  { _giSubst  :: s }
  deriving ( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''Renaming])

termToVar :: VTerm Name LVar -> LVar
termToVar (LIT (Var v)) = v
termToVar _             = error "term is not a variable literal"

renamedTimePoints :: Renaming LNSubst -> [(LVar, LVar)]
renamedTimePoints r =
  let subst = sMap $ L.get giSubst r
      timepoints = filter ((== LSortNode) . lvarSort) $ M.keys subst
  in zip timepoints (map (termToVar . (subst M.!)) timepoints)

type Acc = (M.Map LVar LVar, M.Map LVar LVar, M.Map LVar (VTerm Name LVar))

fromRuleRenaming :: RuleACInst -> RuleACInst -> LNSubstVFresh -> Renaming LNSubst
fromRuleRenaming r1 r2 =
  let rng1 = range r1
      rng2 = range r2
  in Renaming . Subst . mergeAcc . M.foldrWithKey (canonicalize rng1 rng2) (M.empty, M.empty, M.empty) . svMap
  where
    canonicalize :: S.Set LVar -> S.Set LVar -> LVar -> VTerm Name LVar -> Acc -> Acc
    canonicalize rng1 rng2 v t (memd, memdInv, m)
      | tv `S.member` rng2 = (memd, memdInv, M.insert v t m)
      | tv `S.member` rng1 = (memd, memdInv, M.insert tv (LIT $ Var v) m)
      | v `S.member` rng1 = (M.insert v tv memd, memdInv, m)
      | v `S.member` rng2 = (memd, M.insert tv v memdInv, m)
      | otherwise = error "illegal state"
      where tv = termToVar t

    range :: RuleACInst -> S.Set LVar
    range = S.fromList . map fst . varOccurences

    mergeAcc :: Acc -> M.Map LVar (VTerm Name LVar)
    mergeAcc (memd, memdInv, target) =
      M.foldrWithKey (\k v -> M.insert k (LIT $ Var $ memdInv M.! v)) target memd

applyRenaming :: Apply s a => Renaming s -> a -> a
applyRenaming (Renaming s) = apply s

idRenaming :: MaybeMaude (Renaming (Subst c v))
idRenaming = MaybeT $ return $ Just $ Renaming emptySubst

noRenaming :: MaybeMaude (Renaming s)
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

mapVarM :: (IsConst c, IsVar v) => v -> v -> MaybeMaude (Renaming (Subst c v)) -> MaybeMaude (Renaming (Subst c v))
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
  r1 ~> r2 = fromRuleRenaming r1 r2 <$> MaybeT (getRuleRenaming r1 r2)

(~><~) :: (IsConst c, IsVar v) => MaybeRenaming (Subst c v) -> MaybeRenaming (Subst c v) -> MaybeRenaming (Subst c v)
(~><~) lrm rrm = do
  (Renaming lsubst) <- lrm
  (Renaming rsubst) <- rrm
  MaybeT $ return $ Renaming <$> merge lsubst rsubst
  where
    merge :: (IsConst c, IsVar v) => Subst c v -> Subst c v -> Maybe (Subst c v)
    merge (Subst m1) (Subst m2) = Subst <$> mergeMaps m1 m2

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
