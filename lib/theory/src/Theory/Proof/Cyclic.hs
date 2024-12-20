{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Theory.Proof.Cyclic
  ( ProgressingVars(..)
  , BackLink(..)
  , BackLinkEdge
  , toProof
  , CyclicProof(..)
  , ProofSoundness(..)
  , soundness
  , updateFinished ) where

import qualified Data.Set as S
import Theory.Constraint.System.ID
import Term.LTerm
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import qualified Data.Map as M
import Control.Monad
import Utils.PartialOrd (TransClosedOrder(..), PartialOrder (pempty, pinsert), PartialOrdering(..), unionDisjoint)
import Theory.Constraint.Renaming (Renaming)

data ProgressingVars = PVs
  { pvProgresses :: S.Set NodeId
    -- ^ To be understood as <. Hence, is subset of pvPreserves.
  , pvPreserves :: S.Set NodeId
    -- ^ to be understood as <=.
  }
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

instance HasFrees ProgressingVars where
  foldFrees f (PVs prg prsv) = foldFrees f prg <> foldFrees f prsv
  foldFreesOcc _ _ _ = mempty
  mapFrees f (PVs prg prsv)= PVs <$> mapFrees f prg <*> mapFrees f prsv

restrict :: ProgressingVars -> S.Set NodeId -> ProgressingVars
restrict (PVs prog pres) s = PVs (S.intersection prog s) (S.intersection pres s)

type BackLinkEdge = (SystemID, SystemID)

defaultOrderWhenInSCS :: BackLinkEdge -> BackLinkEdge -> Maybe (BackLinkEdge, BackLinkEdge)
defaultOrderWhenInSCS e@(es, et) e'@(es', et') = case checkRelation et et' of
  -- Edges don't form an SCS
  PINCOMP -> Nothing
  -- Strucuture is:
  --     (et = et')
  --  +----> * <-----+
  --  |     / \      |
  --  +-es *   * es'-+
  PEQ -> return (e, e')
  -- Check whether structure is:
  --        * et'<--+
  --        |       |
  -- +----->* et    |
  -- |     / \      |
  -- +-es *   * es'-+
  PLT -> guard (PLT == checkRelation es' et) >> return (e, e')
   -- Check whether structure is:
  --         * et<---+
  --         |       |
  -- +------>* et'   |
  -- |      / \      |
  -- +-es' *   * es--+
  PGT -> guard (PLT == checkRelation es et') >> return (e', e)

data BackLink = BackLink
  { edge :: BackLinkEdge
  , renaming :: Renaming
  , pvs :: ProgressingVars }
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

instance HasFrees BackLink where
  foldFrees f (BackLink _ subst vs) = foldFrees f vs <> foldFrees f subst
  foldFreesOcc _ _ _ = mempty
  mapFrees f (BackLink e subst vs) = BackLink e <$> mapFrees f subst <*> mapFrees f vs

toProof :: BackLink -> CyclicProof
toProof bl@(BackLink e _ pv)
  | S.null (pvProgresses pv) = UnsoundProof
  | otherwise = MaybeSoundProof [] (Just scs)
  where
    scs = SCS e (M.singleton e bl) (InductionOrder pempty (M.singleton e pv))

type VariableMapping = M.Map BackLinkEdge ProgressingVars

data InductionOrder = InductionOrder
  { backLinkOrder :: TransClosedOrder BackLinkEdge
  , variableMapping :: VariableMapping }
  deriving( Show, Eq, Ord, Generic, NFData, Binary )

-- StronglyConnectedSubgraph
data DischargingSCS = SCS
  { maxEdge :: BackLinkEdge
  , backLinks :: M.Map BackLinkEdge BackLink
  , inductionOrder :: InductionOrder }
  deriving( Show, Eq, Ord, Generic, NFData, Binary )

-- |Take the union of two SCSes under two invariants. (1) Their edges must be
--  disjoint. This invariant can easily be established when folding a proof
--  using DFS. (2) Their maxNodes share a path. In pratcice, this invariant
-- means that we do not know yet whether the SCSes form a strongly connected
-- component.
joinSCS :: DischargingSCS -> DischargingSCS -> Maybe DischargingSCS
joinSCS (SCS mexE bls (InductionOrder o vm)) (SCS maxE' bls' (InductionOrder o' vm')) = do
  newEdge <- defaultOrderWhenInSCS mexE maxE'
  -- We can <> the variable maps because we assume their keys are disjoint
  let joinedOrder = InductionOrder (unionDisjoint o o') (vm <> vm')
  let newOrder = orderMaxima newEdge joinedOrder
  -- Check we still progress
  guard (not $ any (null . pvProgresses) $ M.elems (variableMapping newOrder))
  -- We can <> the backlink maps because we assume their keys are disjoint
  let (newMaxE, rest) = S.deleteFindMin $ maxima (backLinkOrder newOrder)
  guard (null rest)  -- Check that new maximal edge is uniquely defined
  return $ SCS newMaxE (bls <> bls') newOrder
  where
    updateVariableMapping :: (BackLinkEdge, BackLinkEdge) -> VariableMapping -> VariableMapping
    updateVariableMapping (sml, lrg) varMap =
      let vars = restrict (varMap M.! lrg) (pvPreserves $ varMap M.! sml)
      in M.insert lrg vars vm

    orderMaxima :: (BackLinkEdge, BackLinkEdge) -> InductionOrder -> InductionOrder
    orderMaxima el (InductionOrder ord varMap) =
      InductionOrder (pinsert el ord) (updateVariableMapping el varMap)

data CyclicProof = UnsoundProof | SoundProof [DischargingSCS] | MaybeSoundProof
  { components :: [DischargingSCS]
  -- ^All discharging subgraphs that are components, i.e., maximal subgraphs.
  , subgraph :: Maybe DischargingSCS
  -- ^A subgraph not yet known to be a component, i.e., may grow larger or not
  -- discharge.
  } deriving( Show, Eq, Ord, Generic, NFData, Binary )

data ProofSoundness = Sound | Unsound | Undetermined

soundness :: CyclicProof -> ProofSoundness
soundness UnsoundProof = Unsound
soundness (SoundProof _) = Sound
soundness (MaybeSoundProof _ _) = Undetermined

instance HasFrees CyclicProof where
  foldFrees _ _ = mempty
  foldFreesOcc _ _ = mempty
  mapFrees _ = pure

instance Semigroup CyclicProof where
  UnsoundProof <> _ = UnsoundProof
  _ <> UnsoundProof = UnsoundProof
  SoundProof sccs <> SoundProof sccs' = SoundProof (sccs ++ sccs')
  SoundProof sccs <> MaybeSoundProof sccs' scs = MaybeSoundProof (sccs ++ sccs') scs
  MaybeSoundProof sccs' scs <> SoundProof sccs = MaybeSoundProof (sccs ++ sccs') scs
  (MaybeSoundProof f uf) <> (MaybeSoundProof f' uf') = MaybeSoundProof (f ++ f') (merge uf uf')
    where
      merge :: Maybe DischargingSCS -> Maybe DischargingSCS -> Maybe DischargingSCS
      merge Nothing _ = Nothing
      merge _ Nothing = Nothing
      merge (Just scs1) (Just scs2) = joinSCS scs1 scs2

updateFinished :: SystemID -> CyclicProof -> CyclicProof
updateFinished _ UnsoundProof = UnsoundProof
updateFinished _ prf@(SoundProof _) = prf
-- | SCS did not discharge
updateFinished _ (MaybeSoundProof _ Nothing) = UnsoundProof
-- | SCS discharged and because we are at @at@ now, we now that the SCS is an
--   SCC.
updateFinished at prf@(MaybeSoundProof sccs (Just discharging))
  | at == snd (maxEdge discharging) = SoundProof (discharging:sccs)
  | otherwise = prf
