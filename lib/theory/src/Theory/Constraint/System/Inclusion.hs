{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
module Theory.Constraint.System.Inclusion
  ( InclusionFailure(..)
  , BackLinkCandidate(..)
  , prefixMatchesOnPath
  , allPrefixMatches ) where

import qualified Extension.Data.Label as L
import qualified Data.Set as S
import Theory.Constraint.System
import Theory.Constraint.System.ID (SystemID)
import Term.LTerm
import Term.Maude.Process (MaudeHandle)
import Theory.Constraint.SystemMatch
import qualified Data.Map as M
import qualified Data.List as L
import Data.List.NonEmpty (NonEmpty((:|)))
import Control.Monad
import Control.Applicative ((<|>))
import Theory.Model.Rule
import Data.Maybe (mapMaybe, maybeToList )
import Theory.Model.Signature (sigmMaudeHandle)
import Theory.Model.Fact (LNFact, FactTag, Fact (factTag))
import Theory.Model.Atom (ProtoAtom(Action, Less))
import Theory.Proof.Cyclic
import Utils.PartialOrd
import Data.Bifunctor (Bifunctor(bimap, first))
import Utils.Two (tuple, mapTwice)
import Utils.Misc (addAt)
import Term.Substitution (Apply(apply), LNSubst)
import Control.Monad.Trans.Reader (runReader)
import Data.Bool (bool)
import Control.Monad.Except (MonadError (throwError))
import Data.Either (partitionEithers)

data Node a = Node
  { nnid  :: NodeId
  , nannot :: a }

instance Show a => Show (Node a) where
  show (Node nid a) = show nid ++ ":" ++ show a

instance Eq a => Eq (Node a) where
  (Node n1 a1) == (Node n2 a2) = n1 == n2 && a1 == a2

instance Ord a => Ord (Node a) where
  compare (Node n1 a1) (Node n2 a2) = case compare n1 n2 of
    LT  -> LT
    GT  -> GT
    EQ  -> compare a1 a2

instance Matchable a => Matchable (Node a) where
  (Node nid1 a1) ~> (Node nid2 a2) = mapNode nid1 nid2 (a1 ~> a2)

type ColoredNode = Node (Either RuleACInst AFGoals)

type Color = Either String [FactTag]

getColor :: ColoredNode -> Color
getColor = bimap getRuleName (map factTag . afgs) . nannot

data BackLinkCandidate = PartialCyclicProof
 { blUpTo :: UpTo
 , bl :: BackLink }
  deriving ( Show )

fromMatch :: BackLinkEdge -> MatchUpToWithVars -> BackLinkCandidate
fromMatch e (m, upTo, progressing) = PartialCyclicProof upTo (BackLink e m progressing)

type MatchUpToWithVars = (LNSubst, UpTo, ProgressingVars)

type AGTuple = (LVar, LNFact)

data InclusionFailure = MissingEdge [Edge] | MissingLesRel [(NodeId, NodeId)] | EqStoreFail | SubTermStoreFail | NoProgress | Internal
  deriving (Eq, Ord, Show)

-- TODO: Handle last
-- TODO: Document @System@ w.r.t. to how this functino works
isProgressingAndSubSysUpTo :: MaudeHandle -> System -> System -> LNSubst -> Either InclusionFailure MatchUpToWithVars
isProgressingAndSubSysUpTo mh smaller larger sub = do
  -- Check edge inclusion
  let edgeDiff = apply sub (L.get sEdges smaller) `S.difference` L.get sEdges larger
  unless (S.null edgeDiff) (throwError (MissingEdge (S.toList edgeDiff)))

  -- Check that all elements in the smaller relation are contained in the larger
  -- relation.
  let lessAtomsSmaller = map (apply sub . lessAtomToEdge) $ S.toList $ L.get sLessAtoms smaller
  lessRelLarger <- maybe (throwError Internal) return $ fromSet (S.fromList (rawLessRel larger))
  let lessRelDiff = filter (not . uncurry (isSmaller lessRelLarger)) lessAtomsSmaller
  let cutLess = S.fromList $ map lessToFormula lessRelDiff

  unless (runReader (eqStoreInlcusionModR sub (L.get sEqStore smaller) (L.get sEqStore larger)) mh) (throwError EqStoreFail)
  let stDiff = apply sub (L.get sSubtermStore smaller) `subtermStoreDiff` L.get sSubtermStore larger

  let varsInSmaller =
            S.fromList (map fst lessAtomsSmaller) <> S.fromList (map snd lessAtomsSmaller)
        <>  M.keysSet (L.get sNodes smaller) <> actionNodes smaller
  let varsInLarger = universe lessRelLarger <> M.keysSet (L.get sNodes larger) <> actionNodes larger

  let pres = varsInSmaller `S.intersection` varsInLarger
  let prog = S.filter (checkProgresses lessRelLarger) pres
  when (S.null prog) (throwError NoProgress)

  let diffFormulas = apply sub (L.get sFormulas smaller) `S.difference` L.get sFormulas larger
  let diffActionGoals = apply sub (actionGoals smaller) `S.difference` actionGoals larger
  return (sub, stDiff <> cutLess <> diffFormulas <> S.map atToFormula diffActionGoals, PVs prog pres)
  where
    actionGoals :: System -> S.Set AGTuple
    actionGoals = S.fromList . unsolvedActionAtoms

    actionNodes :: System -> S.Set NodeId
    actionNodes = S.mapMonotonic fst . actionGoals

    atToFormula :: AGTuple -> LNGuarded
    atToFormula (v, f) = GAto $ Action (LIT $ Var $ Free v) (fmap lTermToBTerm f)

    toBTerm :: NodeId -> BLTerm
    toBTerm = lTermToBTerm . varTerm

    lessToFormula :: (NodeId, NodeId) -> LNGuarded
    lessToFormula (toBTerm -> t1, toBTerm -> t2) = GAto $ Less t1 t2

    checkProgresses :: TransClosedOrder LVar -> LVar -> Bool
    checkProgresses ord j = case viewTerm (apply sub (varTerm j :: LNTerm)) of
      Lit (Var sigma_j) -> isSmaller ord sigma_j j
      _ -> False

allPrefixMatches :: MaudeHandle -> System -> System -> [LNSubst]
allPrefixMatches mh smallerSys largerSys = mapMaybe (runSystemMatch mh) (allNodeMappings smallerSys largerSys)

prefixMatchesUpTo :: MaudeHandle -> System -> System -> [Either InclusionFailure MatchUpToWithVars]
prefixMatchesUpTo mh smaller larger =
  map (isProgressingAndSubSysUpTo mh smaller larger) (allPrefixMatches mh smaller larger)

prefixMatchesOnPath :: ProofContext -> NonEmpty System -> Either [(SystemID, [InclusionFailure])] [BackLinkCandidate]
prefixMatchesOnPath ctx (leaf:|candidates) = concat <$> anyRights (map tryMatch candidates)
  where
    anyRights :: [Either a b] -> Either [a] [b]
    anyRights eithers =
      let (ls, rs) = partitionEithers eithers
      in if null rs then Left ls else Right rs

    hnd :: MaudeHandle
    hnd = L.get sigmMaudeHandle $ L.get pcSignature ctx

    tryMatch :: System -> Either (SystemID, [InclusionFailure]) [BackLinkCandidate]
    tryMatch inner =
      let blEdge = (L.get sId leaf, L.get sId inner)
      in bimap (L.get sId inner,) (map (fromMatch blEdge)) (anyRights (prefixMatchesUpTo hnd inner leaf))

-- | Explores all possible matchess between two lists while trying to reject as
--   many candidates as possible. The applicative monoid @m b@ can be used as an
--   accumulator. Whenever two elements of type @a@ are chosen to be matched to
--   one another, the accumulator will be called and should return and update
--   function (within the monoid). After a complete match has been generated,
--   the test function will be called, and the candidate is only considered when
--   the test function returns @True@.
allMappings :: Semigroup s =>
      (a -> a -> SystemMatch)
  -- ^ Function to generate a match
  ->  (a -> a -> (s -> s))
  -- ^ Function to update the testing semigroup
  ->  s
  -- ^ Initial accumulator for semigroup
  ->  SystemMatch
  -- ^ Matching to extend
  ->  [a]
  -- ^ List of left-candidates for mathcings
  ->  [a]
  -- ^ List of right-candidates for matchings. Can be larger than list of left
  --   candidates.
  ->  [(s, SystemMatch)]
  -- ^ Potential matchings with the accumulator
allMappings _ _ _ NoSystemMatch _ _ = []
allMappings _ _ acc r [] _ = [(acc, r)]
allMappings (~~>) genF baseM baseR als ars = rec baseM als ars
  where
    rec m [] _ = [(m, baseR)]
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
      (a -> a -> SystemMatch)
  -- ^ Function to generate a matching
  ->  (a -> a -> (m -> m))
  -- ^ Function to update the testing monoid
  ->  SystemMatch
  -- ^ Matching to extend
  ->  M.Map k [a]
  -- ^ List of left-candidates for matchings
  ->  M.Map k [a]
  -- ^ List of right-candidates for matchings. Can be larger than list of left
  --   candidates.
  ->  [(m, SystemMatch)]
  -- ^ Potential matchings with the accumulator
allMappingsGrouped _ _ NoSystemMatch _ _ = []
allMappingsGrouped (~~>) genF baseR als ars
  | M.null als = [(mempty, baseR)]
  | otherwise =
    let pairs = M.foldrWithKey foldToMatching (Just []) als
        -- ^ First look whether we have a matching key in the right map for every
        --   key in the left map. This is more efficient than exploring matchings
        --   and thus should help with early termination.
    in  maybe [] (foldr (\(as, as') -> concatMap (allMs as as')) [(mempty, baseR)]) pairs
  where
    allMs as as' (accM, r) = allMappings (~~>) genF accM r as as'
    foldToMatching k as ml = do
      l <- ml
      as' <- M.lookup k ars
      guard (length as <= length as')
      return $ (as, as'):l

-- | Tries to match loops to one another s.t. some of the matched loops
--   *could* make progress. We early-test whether we could make progress by
--   checking that whether some loop is shorter than the loop it got mapped to.
--   If no loops are provided, we say there are no matchings. Technically, the
--   identity would be a valid matchings, but this matching will not make
--   progress. We expect that only matchings of loops will progress.
allLoopMappings :: [LoopInstance ColoredNode] -> [LoopInstance ColoredNode] -> [SystemMatch]
allLoopMappings [] _ = []
allLoopMappings _ [] = []
allLoopMappings lisSml lisLrg =
    map snd
  $ allMappingsGrouped (~>) (\_ _ _ -> ()) mempty (groupF lisSml) (groupF lisLrg)
  where
    groupF :: [LoopInstance ColoredNode] -> M.Map Color [LoopInstance ColoredNode]
    groupF = groupByColor (getColor . start)

mapAlongEdges :: (Matchable a, Ord a, Ord k) =>
     (a -> NodeId)
  -> ([a] -> M.Map k [a])
  -> M.Map a (S.Set a)
  -> M.Map a (S.Set a)
  -> [a]
  -> [a]
  -> SystemMatch
  -> [SystemMatch]
mapAlongEdges nidF groupF topoSml topoLrg = go
  where
    go [] _ r = [r]
    go ns1 ns2 r =
      let (mapped1, notMapped1) = L.partition ((`S.member` graphDomain r) . nidF) ns1
          (mapped2, notMapped2) = L.partition ((`S.member` graphImage r) . nidF) ns2
          mapped2M = M.fromList (map (\a -> (nidF a, a)) mapped2)
          mapped = mapMaybe (getMappedTo mapped2M) mapped1
          rs = allMappingsGrouped (~>) (\a1 a2 -> ((a1, a2):)) r (groupF notMapped1) (groupF notMapped2)
      in concatMap (uncurry rec . first (mapped ++)) rs
      where
        getMappedTo m a = do
          to <- (`M.lookup` m) =<< M.lookup (nidF a) (graphMatch r)
          return (a, to)

    largerIn :: Ord k => M.Map k (S.Set a) -> k -> [a]
    largerIn m = maybe [] S.toList . (m M.!?)

    rec [] r = [r]
    rec mappedNodes r =
      let larger = map (bimap (largerIn topoSml) (largerIn topoLrg)) mappedNodes
      in foldr (\(ns1, ns2) -> concatMap (go ns1 ns2)) [r] larger

colorAnnotated :: System -> NodeId -> Maybe ColoredNode
colorAnnotated s nid = Node nid . Left <$> M.lookup nid (L.get sNodes s)

colorAFG :: AFMap -> NodeId -> Maybe ColoredNode
colorAFG afs nid = Node nid . Right . AFGoals <$> M.lookup nid afs

colorNid :: System -> AFMap -> NodeId -> Maybe ColoredNode
colorNid s afs nid = colorAnnotated s nid <|> colorAFG afs nid

toposortedEdges :: System -> AFMap -> Maybe (TransClosedOrder ColoredNode, TransClosedOrder ColoredNode)
toposortedEdges s afs =
  let lessRel = colorList (colorNid s afs) (rawLessRel s)
      nodeRel = colorList (colorAnnotated s) (rawEdgeRel s)
      afNodes = S.fromList $ map mkAFG (M.toList afs) :: S.Set ColoredNode
      nodes = map mkAnnotated (M.toList $ L.get sNodes s) :: [ColoredNode]
  in do
    nodeOrder <- fromSet (S.fromList nodeRel)
    let withLess = foldr pinsert nodeOrder lessRel
    return (foldr addAsUnordered nodeOrder nodes, restrict (`S.member` afNodes) (foldr addAsUnordered withLess afNodes))
  where
    colorList :: Ord a => (a -> Maybe ColoredNode) -> [(a, a)] -> [(ColoredNode, ColoredNode)]
    colorList f = mapMaybe (fmap tuple . sequence . mapTwice f)

    mkAFG :: (NodeId, [LNFact]) -> ColoredNode
    mkAFG = uncurry Node . fmap (Right . AFGoals)

    mkAnnotated :: (NodeId, RuleACInst) -> ColoredNode
    mkAnnotated = uncurry Node . fmap Left

type AFMap = M.Map NodeId [LNFact]

loops :: System -> [LoopInstance ColoredNode]
loops s = mapMaybe (traverse (colorAnnotated s)) (L.get sLoops s)

unsolvedAFGoals :: System -> AFMap
unsolvedAFGoals s =
  let afts = unsolvedActionAtoms s
  in foldr (uncurry addAt) M.empty afts

loopsAndsystemSpanningOrder :: System -> Maybe ([LoopInstance ColoredNode], TransClosedOrder ColoredNode, TransClosedOrder ColoredNode)
loopsAndsystemSpanningOrder s = do
  let afs = unsolvedAFGoals s
  (nodeOrd, afLessOrd) <- toposortedEdges s afs
  let ls = loops s
  let roots = startFrom nodeOrd ls
  let (spanning, rest) = spanningOrder (toRawRelation nodeOrd) roots
  guard (null rest)
  return (ls, foldr addAsUnordered spanning (unordered nodeOrd), afLessOrd)
  where
    startFrom :: TransClosedOrder ColoredNode -> [LoopInstance ColoredNode] -> S.Set ColoredNode
    startFrom ord ls =
      let roots = foldr skipFr S.empty (minima ord)
          starts = map start ls
      in  foldr S.insert (S.filter ((`all` starts) . cannotReach) roots) starts
      where
        cannotReach :: ColoredNode -> ColoredNode -> Bool
        cannotReach from to = not $ to `S.member` getLarger ord from

        skipFr :: ColoredNode -> S.Set ColoredNode -> S.Set ColoredNode
        skipFr n = bool (S.insert n) (S.union (getDirectlyLarger ord n)) (either isFreshRule (const False) (nannot n))

groupByColor :: (a -> Color) -> [a] -> M.Map Color [a]
groupByColor f = foldr (\n -> addAt (f n) n) M.empty

allNodeMappings :: System -> System -> [SystemMatch]
allNodeMappings smaller larger = do
  (lsSml, spanningSml, afsOrdSml) <- maybeToList (loopsAndsystemSpanningOrder smaller)
  (lsLrg, spanningLrg, afsOrdLrg) <- maybeToList (loopsAndsystemSpanningOrder larger)
  r0 <- if null lsSml then [mempty] else allLoopMappings lsSml lsLrg
  r1 <- mapF (raw spanningSml) (raw spanningLrg) (startAt spanningSml) (startAt spanningLrg) r0
  mapF (toGreater afsOrdSml) (toGreater afsOrdLrg) (startAt afsOrdSml) (startAt afsOrdLrg) r1
  where
    mapF = mapAlongEdges nnid (groupByColor getColor)

    startAt :: TransClosedOrder ColoredNode -> [ColoredNode]
    startAt = S.toList . minima
