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
import qualified Data.List.NonEmpty as NE
import Control.Monad
import Control.Applicative ((<|>))
import Theory.Model.Rule
import Data.Maybe (mapMaybe, maybeToList )
import Theory.Model.Signature (sigmMaudeHandle)
import Theory.Model.Fact (LNFact, FactTag, Fact (factTag, factTerms))
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

data TermKind = KFun FunSym | KConst | KVar LSort deriving (Show, Ord, Eq)
termKind :: LNTerm -> TermKind
termKind t = case viewTerm t of
  FApp sym _ -> KFun sym
  Lit (Con _) -> KConst
  Lit (Var (LVar _ sort _)) -> KVar sort

type ColoredNode = Node (Either RuleACInst AFGoals)

type Color = Either String [(FactTag, [TermKind])]

getColor :: ColoredNode -> Color
getColor = bimap getRuleName (map afColor . afgs) . nannot
  where
    afColor :: LNFact -> (FactTag, [TermKind])
    afColor f = (factTag f, [])

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
  unless (isEmptySubtermStore $ L.get sSubtermStore smaller) (throwError SubTermStoreFail)

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

  let varsInSmaller =
            S.fromList (map fst lessAtomsSmaller) <> S.fromList (map snd lessAtomsSmaller)
        <>  M.keysSet (L.get sNodes smaller) <> actionNodes smaller
  let varsInLarger = universe lessRelLarger <> M.keysSet (L.get sNodes larger) <> actionNodes larger

  let pres = varsInSmaller `S.intersection` varsInLarger
  let prog = S.filter (checkProgresses lessRelLarger) pres
  when (S.null prog) (throwError NoProgress)

  let diffFormulas = apply sub (L.get sFormulas smaller) `S.difference` L.get sFormulas larger
  let diffActionGoals = apply sub (actionGoals smaller) `S.difference` actionGoals larger
  return (sub, cutLess <> diffFormulas <> S.map atToFormula diffActionGoals, PVs prog pres)
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
  ->  (s -> Bool)
  -- ^ Test function to early-reject a match candiate
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
allMappings _ _ _ _ NoSystemMatch _ _ = []
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
      (a -> a -> SystemMatch)
  -- ^ Function to generate a matching
  ->  (a -> a -> (m -> m))
  -- ^ Function to update the testing monoid
  ->  (m -> Bool)
  -- ^ Test function to early-reject a matching candiate
  ->  SystemMatch
  -- ^ Matching to extend
  ->  M.Map k [a]
  -- ^ List of left-candidates for matchings
  ->  M.Map k [a]
  -- ^ List of right-candidates for matchings. Can be larger than list of left
  --   candidates.
  ->  [(m, SystemMatch)]
  -- ^ Potential matchings with the accumulator
allMappingsGrouped _ _ _ NoSystemMatch _ _ = []
allMappingsGrouped (~~>) genF testF baseR als ars
  | M.null als = [(mempty, baseR)]
  | otherwise =
    let pairs = M.foldrWithKey foldToMatching (Just []) als
        -- ^ First look whether we have a matching key in the right map for every
        --   key in the left map. This is more efficient than exploring matchings
        --   and thus should help with early termination.
    in  maybe [] (foldr (\(as, as') -> concatMap (allMs as as')) [(mempty, baseR)]) pairs
  where
    allMs as as' (accM, r) = allMappings (~~>) genF testF accM r as as'
    foldToMatching k as ml = do
      l <- ml
      as' <- M.lookup k ars
      guard (length as <= length as')
      return $ (as, as'):l

newtype Or = Any Bool

instance Semigroup Or where
  (Any b1) <> (Any b2) = Any (b1 || b2)

instance Monoid Or where
  mempty = Any False

-- | Tries to match loops to one another s.t. some of the matched loops
--   *could* make progress. We early-test whether we could make progress by
--   checking that whether some loop is shorter than the loop it got mapped to.
--   If no loops are provided, we say there are no macthings. Technically, the
--   identity would be a valid matchings, but this matching will not make
--   progress. We expect that only matchings of loops will progress.
allLoopMappings :: [LoopInstance ColoredNode] -> [LoopInstance ColoredNode] -> [SystemMatch]
allLoopMappings [] _ = []
allLoopMappings _ [] = []
allLoopMappings lisSml lisLrg =
    map snd
  $ filter (didProgress . fst)
  $ allMappingsGrouped (~>) couldProgress (const True) mempty (groupF lisSml) (groupF lisLrg)
  where
    groupF :: [LoopInstance ColoredNode] -> M.Map Color [LoopInstance ColoredNode]
    groupF = groupByColor (getColor . start)

    leftShorter :: NE.NonEmpty a -> NE.NonEmpty a -> Bool
    leftShorter (NE.toList -> l) (NE.toList -> r) = rec l r
      where
        rec [] [] = False
        rec [] _ = True
        rec _ [] = False
        rec (_:tl) (_:tr) = rec tl tr

    couldProgress :: LoopInstance ColoredNode -> LoopInstance ColoredNode -> (Or -> Or)
    couldProgress l1 l2 = (Any (leftShorter (loopEdges l1) (loopEdges l2)) <>)

    didProgress :: Or -> Bool
    didProgress (Any p) = p

mapAlongEdges :: (Matchable a, Ord a, Ord k) =>
     (a -> NodeId)
  -> ([a] -> M.Map k [a])
  -> TransClosedOrder a
  -> TransClosedOrder a
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
          rs = allMappingsGrouped (~>) (\a1 a2 -> ((a1, a2):)) (const True) r (groupF notMapped1) (groupF notMapped2)
      in concatMap (uncurry rec . first (mapped ++)) rs
      where
        getMappedTo m a = do
          to <- (`M.lookup` m) =<< M.lookup (nidF a) (graphMatch r)
          return (a, to)

    rec [] r = [r]
    rec mappedNodes r =
      let larger = map (bimap (S.toList . getDirectlyLarger topoSml) (S.toList . getDirectlyLarger topoLrg)) mappedNodes
      in foldr (\(ns1, ns2) -> concatMap (go ns1 ns2)) [r] larger

colorAnnotated :: System -> NodeId -> Maybe ColoredNode
colorAnnotated s nid = Node nid . Left <$> M.lookup nid (L.get sNodes s)

colorAFG :: AFMap -> NodeId -> Maybe ColoredNode
colorAFG afs nid = Node nid . Right . AFGoals <$> M.lookup nid afs

colorNid :: System -> AFMap -> NodeId -> Maybe ColoredNode
colorNid s afs nid = colorAnnotated s nid <|> colorAFG afs nid

toposortedEdges :: System -> AFMap -> Maybe (TransClosedOrder ColoredNode)
toposortedEdges s afs =
  let kRelRaw = colorList (colorNid s afs) (kLessRel s)
      nodeRel = colorList (colorAnnotated s) (rawEdgeRel s)
      afNodes = map mkAFG (M.toList afs) :: [ColoredNode]
      nodes = map mkAnnotated (M.toList $ L.get sNodes s) :: [ColoredNode]
  in do
    kRel <- toRelation <$> fromSet (S.fromList kRelRaw)
    ord <- fromSet (S.fromList nodeRel <> S.fromList kRel)
    return $ foldr addAsUnordered ord (afNodes ++ nodes)
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

loopsAndsystemSpanningOrder :: System -> Maybe ([LoopInstance ColoredNode], TransClosedOrder ColoredNode)
loopsAndsystemSpanningOrder s = do
  let afs = unsolvedAFGoals s
  es <- toposortedEdges s afs
  let ls = loops s
  let roots = startFrom es ls
  let (rest, spanning) = spanningOrder roots (toRawRelation es)
  unless (M.null rest) (error "spanning DAG computation invariant violated")
  return (ls, foldr addAsUnordered spanning (unordered es))
  where
    startFrom :: TransClosedOrder ColoredNode -> [LoopInstance ColoredNode] -> S.Set ColoredNode
    startFrom ord ls =
      let roots = foldr skipFr S.empty (minima ord)
          starts = map start ls
      in  foldr S.insert (S.filter ((`all` starts) . cannotReach ) roots) starts
      where
        cannotReach :: ColoredNode -> ColoredNode -> Bool
        cannotReach from to = not $ to `S.member` getLarger ord from

        skipFr :: ColoredNode -> S.Set ColoredNode -> S.Set ColoredNode
        skipFr n = bool (S.insert n) (S.union (getDirectlyLarger ord n)) (either isFreshRule (const False) (nannot n))

groupByColor :: (a -> Color) -> [a] -> M.Map Color [a]
groupByColor f = foldr (\n -> addAt (f n) n) M.empty

allNodeMappings :: System -> System -> [SystemMatch]
allNodeMappings smaller larger = do
  (lsSml, spanningSml) <- maybeToList (loopsAndsystemSpanningOrder smaller)
  (lsLrg, spanningLrg) <- maybeToList (loopsAndsystemSpanningOrder larger)
  r0 <- if null lsSml then [mempty] else allLoopMappings lsSml lsLrg
  mapAlongEdges nnid (groupByColor getColor) spanningSml spanningLrg (startAt spanningSml) (startAt spanningLrg) r0
  where
    startAt :: TransClosedOrder ColoredNode -> [ColoredNode]
    startAt = S.toList . minima
