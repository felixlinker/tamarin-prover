{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
module Theory.Constraint.System.Inclusion
  ( BackLinkCandidate(..)
  , getCycleRenamingsOnPath
  , getCycleRenamingOnPath
  , canCloseCycle
  , allRenamings ) where

import qualified Extension.Data.Label as L
import qualified Data.Set as S
import Theory.Constraint.System
import Term.LTerm
import Term.Maude.Process (MaudeHandle)
import Theory.Constraint.Renaming
import qualified Data.Map as M
import qualified Data.List as L
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NE
import Control.Applicative ((<|>))
import Control.Monad
import Theory.Model.Rule
import Data.Maybe (mapMaybe, listToMaybe, maybeToList )
import Theory.Model.Signature (sigmMaudeHandle)
import Theory.Model.Fact (LNFact, FactTag, Fact (factTag))
import Theory.Model.Atom (ProtoAtom(Action))
import Theory.Proof.Cyclic
import Utils.PartialOrd (TransClosedOrder (..), fromSet, image, minima, domain, getDirectlyLarger, isSmaller, universe)
import Data.Bifunctor (Bifunctor(bimap, first))
import Utils.Two (tuple, two, Two)
import Utils.Misc (addAt)
import Term.Substitution (Apply(apply))

data BackLinkCandidate = PartialCyclicProof Renaming UpTo BackLink
  deriving ( Show )

fromCandidate :: BackLinkCandidate -> Maybe BackLink
fromCandidate (PartialCyclicProof _ upTo bl) = guard (S.null upTo) >> return bl

-- |  @Nothing@ is an incorrect renaming, @Just S.Empty@ is a correct renaming,
--    and everything else a potentially correct renaming.
type RenamingUpToWithVars = Maybe (Renaming, UpTo, ProgressingVars)

type AGTuple = (LVar, LNFact)

-- TODO: Handle last
-- TODO: Document @System@ w.r.t. to how this functino works
isProgressingAndSubSysUpTo :: System -> System -> Renaming -> RenamingUpToWithVars
isProgressingAndSubSysUpTo smaller larger renaming = do
  let r = toSubst renaming
  guard (apply r (L.get sEdges smaller) `S.isSubsetOf` L.get sEdges larger)
  let lessAtomsSmaller = map lessAtomToEdge $ S.toList $ L.get sLessAtoms smaller
  lessRelLarger <- fromSet (S.fromList (rawLessRel larger))
  -- Check that all elements in the smaller relation are contained in the larger
  -- relation.
  guard (all (uncurry (isSmaller lessRelLarger) . apply r) lessAtomsSmaller)

  let varsInSmaller =
            S.fromList (map fst lessAtomsSmaller) <> S.fromList (map snd lessAtomsSmaller)
        <>  M.keysSet (L.get sNodes smaller) <> actionNodes smaller
  let varsInLarger = universe lessRelLarger <> M.keysSet (L.get sNodes larger) <> actionNodes larger

  let pres = varsInSmaller `S.intersection` varsInLarger
  let prog = S.filter (checkProgresses lessRelLarger renaming) pres
  guard (not $ S.null prog)

  let diffFormulas = apply r (L.get sFormulas smaller) `S.difference` L.get sFormulas larger
  let diffActionGoals = apply r (actionGoals smaller) `S.difference` actionGoals larger
  return (renaming, diffFormulas <> S.map atToFormula diffActionGoals, PVs prog pres)
  where
    actionGoals :: System -> S.Set AGTuple
    actionGoals = S.fromList . unsolvedActionAtoms

    actionNodes :: System -> S.Set NodeId
    actionNodes = S.mapMonotonic fst . actionGoals

    atToFormula :: AGTuple -> LNGuarded
    atToFormula (v, f) = GAto $ Action (LIT $ Var $ Free v) (fmap lTermToBTerm f)

    checkProgresses :: TransClosedOrder LVar -> Renaming -> LVar -> Bool
    checkProgresses ord (Renaming subst _) j =
      maybe False (\sigma_j -> isSmaller ord sigma_j j) (M.lookup j subst)

rnode :: System -> NodeId -> Maybe RNode
rnode sys nid = Node nid <$> M.lookup nid (L.get sNodes sys)

allRenamings :: MaudeHandle -> System -> System -> [Renaming]
allRenamings mh smallerSys largerSys
  | null (renamableLoops smallerSys) = []
  | otherwise = mapMaybe (runRenaming mh) (allNodeMappings smallerSys largerSys)
  where
    renamableLoops :: System -> [LoopInstance RNode]
    renamableLoops s = mapMaybe (traverse (rnode s)) $ filter (not . hasLoopExit s) (L.get sLoops s)

isContainedInModRenamingUpTo :: MaudeHandle -> System -> System -> RenamingUpToWithVars
isContainedInModRenamingUpTo mh smaller larger =
  msum $ map (isProgressingAndSubSysUpTo smaller larger) (allRenamings mh smaller larger)

getCycleRenamingsOnPath :: ProofContext -> NonEmpty System -> [BackLinkCandidate]
getCycleRenamingsOnPath ctx (leaf:|candidates) = mapMaybe tryRenaming candidates
  where
    hnd :: MaudeHandle
    hnd = L.get sigmMaudeHandle $ L.get pcSignature ctx

    tryRenaming :: System -> Maybe BackLinkCandidate
    tryRenaming inner = do
      (r, upTo, progressing) <- isContainedInModRenamingUpTo hnd inner leaf
      return $ PartialCyclicProof r upTo (BackLink (L.get sId leaf, L.get sId inner) (rsubst r) progressing)

getCycleRenamingOnPath :: ProofContext -> NonEmpty System -> Maybe BackLinkCandidate
getCycleRenamingOnPath ctx = listToMaybe . getCycleRenamingsOnPath ctx

canCloseCycle :: ProofContext -> NonEmpty System -> Maybe BackLink
canCloseCycle ctx p = getCycleRenamingOnPath ctx p >>= fromCandidate

-- | Explores all possible renamings between two lists while trying to reject as
--   many candidates as possible. The applicative monoid @m b@ can be used as an
--   accumulator. Whenever two elements of type @a@ are chosen to be renamed to
--   one another, the accumulator will be called and should return and update
--   function (within the monoid). After a complete renaming has been generated,
--   the test function will be called, and the candidate is only considered when
--   the test function returns @True@.
allMappings :: Semigroup s =>
      (a -> a -> PartialRenaming)
  -- ^ Function to generate a renaming
  ->  (a -> a -> (s -> s))
  -- ^ Function to update the testing semigroup
  ->  (s -> Bool)
  -- ^ Test function to early-reject a renaming candiate
  ->  s
  -- ^ Initial accumulator for semigroup
  ->  PartialRenaming
  -- ^ Renaming to extend
  ->  [a]
  -- ^ List of left-candidates for renamings
  ->  [a]
  -- ^ List of right-candidates for renamings. Can be larger than list of left
  --   candidates.
  ->  [(s, PartialRenaming)]
  -- ^ Potential renamings with the accumulator
allMappings _ _ _ _ NoRenaming _ _ = []
allMappings _ _ testF acc r [] _ = [(acc, r) | testF acc]
allMappings (~~>) genF testF baseM baseR als ars = rec baseM als ars
  where
    rec m [] _ = [(m, baseR) | testF m]
    rec _ _ [] = []
    rec m (a:as) la' = withListAcc [] la'
      where
        withListAcc _ [] = []
        withListAcc lacc (a':as') =
          let m' = genF a a' m
              mappedTail = rec m' as (lacc ++ as')
              differentlyMappedHead = withListAcc (lacc ++ [a']) as'
          in extendWith (a ~~> a') mappedTail ++ differentlyMappedHead

allMappingsGrouped :: (Ord k, Monoid m) =>
      (a -> a -> PartialRenaming)
  -- ^ Function to generate a renaming
  ->  (a -> a -> (m -> m))
  -- ^ Function to update the testing monoid
  ->  (m -> Bool)
  -- ^ Test function to early-reject a renaming candiate
  ->  PartialRenaming
  -- ^ Renaming to extend
  ->  M.Map k [a]
  -- ^ List of left-candidates for renamings
  ->  M.Map k [a]
  -- ^ List of right-candidates for renamings. Can be larger than list of left
  --   candidates.
  ->  [(m, PartialRenaming)]
  -- ^ Potential renamings with the accumulator
allMappingsGrouped _ _ _ NoRenaming _ _ = []
allMappingsGrouped (~~>) genF testF baseR als ars
  | M.null als = [(mempty, baseR)]
  | otherwise =
    let pairs = M.foldrWithKey foldToMatching (Just []) als
        -- ^ First look whether we have a matching key in the right map for every
        --   key in the left map. This is more efficient than exploring renamings
        --   and thus should help with early termination.
    in  maybe [] (foldr (\(as, as') -> concatMap (allMs as as')) [(mempty, baseR)]) pairs
  where
    allMs as as' (accM, r) = allMappings (~~>) genF testF accM r as as'
    foldToMatching k as ml = do
      l <- ml
      as' <- M.lookup k ars
      return $ (as, as'):l

newtype Or = Any Bool

instance Semigroup Or where
  (Any b1) <> (Any b2) = Any (b1 || b2)

instance Monoid Or where
  mempty = Any False

groupByNode :: (a -> RNode) -> [a] -> M.Map String [a]
groupByNode f = foldr (uncurry addAt . withNodeName) M.empty
  where
    withNodeName fn = (show $ getRuleName (nannot (f fn)), fn)

groupByFacts :: [AFNode] -> M.Map [FactTag] [AFNode]
groupByFacts = foldr (uncurry addAt . withFacts) M.empty
  where
    withFacts a = (map factTag (nannot a), a)

type Mapping = (RNode, RNode)

-- | Tries to rename loops into one another s.t. some of the renamed loops
--   *could* make progress. We early-test whether we could make progress by
--   checking that whether some loop is shorter than the loop it got mapped to.
--   If no loops are provided, we say there are no renamings. Technically, the
--   identity would be a valid renamings, but this renaming will not make
--   progress. We expect that only renamings of loops will progress.
allLoopMappings :: [LoopInstance RNode] -> [LoopInstance RNode] -> [([Mapping], PartialRenaming)]
allLoopMappings [] _ = []
allLoopMappings _ [] = []
allLoopMappings lisSml lisLrg =
    map (first fst)
  $ filter (didProgress . fst)
  $ allMappingsGrouped (~>) couldProgress (const True) (Pure idRenaming) (groupByNode start lisSml) (groupByNode start lisLrg)
  where
    leftShorter :: NE.NonEmpty a -> NE.NonEmpty a -> Bool
    leftShorter (NE.toList -> l) (NE.toList -> r) = rec l r
      where
        rec [] [] = False
        rec [] _ = True
        rec _ [] = False
        rec (_:tl) (_:tr) = rec tl tr

    couldProgress :: LoopInstance RNode -> LoopInstance RNode -> (([Mapping], Or) -> ([Mapping], Or))
    couldProgress l1 l2 =
      let end = NE.last $ NE.zip (loopEdges l1) (loopEdges l2)
      in bimap (end:) (Any (leftShorter (loopEdges l1) (loopEdges l2)) <>)

    didProgress :: ([Mapping], Or) -> Bool
    didProgress (_, Any p) = p

mapAlongEdges :: (Renamable a, Ord a, Ord k) =>
     (a -> NodeId)
  -> ([a] -> M.Map k [a])
  -> TransClosedOrder a
  -> TransClosedOrder a
  -> [a]
  -> [a]
  -> PartialRenaming
  -> [PartialRenaming]
mapAlongEdges nidF groupF topoSml topoLrg = go
  where
    go [] _ r = [r]
    go ns1 ns2 r =
      let (mapped1, notMapped1) = L.partition ((`S.member` nonMonadicDomain r) . nidF) ns1
          (mapped2, notMapped2) = L.partition ((`S.member` nonMonadicImage r) . nidF) ns2
          mapped2M = M.fromList (map (\a -> (nidF a, a)) mapped2)
          mapped = mapMaybe (getMappedTo mapped2M) mapped1
          rs = allMappingsGrouped (~>) (\a1 a2 -> ((a1, a2):)) (const True) r (groupF notMapped1) (groupF notMapped2)
      in concatMap (uncurry rec . first (mapped ++)) rs
      where
        getMappedTo m a = do
          to <- M.lookup (applyR (nonMonadicRenaming r) (nidF a)) m
          return (a, to)

    rec [] r = [r]
    rec mappedNodes r =
      let larger = map (bimap (S.toList . getDirectlyLarger topoSml) (S.toList . getDirectlyLarger topoLrg)) mappedNodes
      in foldr (\(ns1, ns2) -> concatMap (go ns1 ns2)) [r] larger

toposortedRel :: Ord a => (NodeId -> Maybe a) -> [Two NodeId] -> Maybe (TransClosedOrder a)
toposortedRel f = fromSet . S.fromList . mapMaybe (fmap tuple . traverse f)

-- | Generate the transitive closure of the edge relaiton of the constraint
--   system, but in inverted order so that the maxima of the relation are the
--   nodes that have no premise solved (or no premise).
toposortedNodeRel :: System -> Maybe (TransClosedOrder RNode)
toposortedNodeRel s = toposortedRel (rnode s) (map (uncurry two) (rawEdgeRel s))

toposortedKRel :: System -> Maybe (TransClosedOrder RNode)
toposortedKRel s = toposortedRel (rnode s) (map (uncurry two) (kLessRel s))

type AFMap = M.Map NodeId AFNode

toposortedAFRel :: System -> AFMap -> Maybe (AFMap, TransClosedOrder AFNode)
toposortedAFRel sys afs = do
  order <- toposortedRel afnode (map (uncurry two) $ filter p (kLessRel sys))
  let ordered = image order <> domain order
  return (M.filter (`S.notMember` ordered) afs, order)
  where
    afnode :: NodeId -> Maybe AFNode
    afnode nid = nid `M.lookup` afs <|> Just (Node nid [])

    p :: (NodeId, NodeId) -> Bool
    p (lt, gt) = (lt `M.member` afs) || (gt `M.member` afs)

loops :: System -> [LoopInstance RNode]
loops s = mapMaybe (traverse (rnode s)) (L.get sLoops s)

splitByK :: System -> ([RNode], [RNode])
splitByK sys =
  let nodes = L.get sNodes sys
  in L.partition (isIntruderRule . nannot) $ map (uncurry Node) (M.toList nodes)

unsolvedAFGoals :: System -> AFMap
unsolvedAFGoals s =
  let afts = unsolvedActionAtoms s
  in M.mapWithKey Node (foldr (uncurry addAt) M.empty afts)

rootsIn :: TransClosedOrder RNode -> [RNode] -> [RNode]
rootsIn tco baseNodes =
  let notMinima = image tco
  in filter (`S.notMember` notMinima) baseNodes

getMappingInput :: System -> Maybe ([LoopInstance RNode], TransClosedOrder RNode, [RNode], TransClosedOrder RNode, [RNode], TransClosedOrder AFNode, [AFNode])
getMappingInput s = do
  let ls = loops s
  topo <- toposortedNodeRel s
  let (nodesK, nodesNotK) = splitByK s
  let roots = rootsIn topo nodesNotK
  kTopo <- toposortedKRel s
  let kRoots = rootsIn kTopo nodesK
  (unordered, afTopo) <- toposortedAFRel s $ unsolvedAFGoals s
  let afRoots = S.toList $ minima afTopo
  return (ls, topo, roots, kTopo, kRoots, afTopo, M.elems unordered ++ afRoots)

allNodeMappings :: System -> System -> [PartialRenaming]
allNodeMappings sml lrg = do
  (lsSml, topoSml, rootsSml, kTopoSml, kRootsSml, afTopoSml, afRootsSml) <- maybeToList $ getMappingInput sml
  (lsLrg, topoLrg, rootsLrg, kTopoLrg, kRootsLrg, afTopoLrg, afRootsLrg) <- maybeToList $ getMappingInput lrg

  (mappedEnds, r1) <- allLoopMappings lsSml lsLrg
  r2 <- mapAlongEdges nnid (groupByNode id) topoSml topoLrg (map fst mappedEnds) (map snd mappedEnds) r1
  r3 <- mapAlongEdges nnid (groupByNode id) topoSml topoLrg rootsSml rootsLrg r2
  r4 <- mapAlongEdges nnid (groupByNode id) kTopoSml kTopoLrg kRootsSml kRootsLrg r3
  mapAlongEdges nnid groupByFacts afTopoSml afTopoLrg afRootsSml afRootsLrg r4
