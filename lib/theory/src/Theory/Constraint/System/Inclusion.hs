{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
module Theory.Constraint.System.Inclusion
  ( BackLinkCandidate(..)
  , getCycleRenamingsOnPath
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
import Control.Monad
import Control.Applicative ((<|>))
import Theory.Model.Rule
import Data.Maybe (mapMaybe, maybeToList )
import Theory.Model.Signature (sigmMaudeHandle)
import Theory.Model.Fact (LNFact, FactTag, Fact (factTag, factTerms))
import Theory.Model.Atom (ProtoAtom(Action))
import Theory.Proof.Cyclic
import Utils.PartialOrd
import Data.Bifunctor (Bifunctor(bimap, first))
import Utils.Two (tuple, mapTwice)
import Utils.Misc (addAt)
import Term.Substitution (Apply(apply))
import Control.Monad.Trans.Reader (runReader)
import Data.Bool (bool)

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

instance Renamable a => Renamable (Node a) where
  (Node nid1 a1) ~> (Node nid2 a2) = mapVarM nid1 nid2 (a1 ~> a2)

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
    afColor f = (factTag f, map termKind (factTerms f))

data BackLinkCandidate = PartialCyclicProof
 { blUpTo :: UpTo
 , bl :: BackLink }
  deriving ( Show )

fromRenaming :: BackLinkEdge -> RenamingUpToWithVars -> BackLinkCandidate
fromRenaming e (r, upTo, progressing) = PartialCyclicProof upTo (BackLink e r progressing)

type RenamingUpToWithVars = (Renaming, UpTo, ProgressingVars)

type AGTuple = (LVar, LNFact)

-- TODO: Handle last
-- TODO: Document @System@ w.r.t. to how this functino works
isProgressingAndSubSysUpTo :: MaudeHandle -> System -> System -> Renaming -> Maybe RenamingUpToWithVars
isProgressingAndSubSysUpTo mh smaller larger renaming = do
  let r = toSubst renaming
  guard (apply r (L.get sEdges smaller) `S.isSubsetOf` L.get sEdges larger)
  let lessAtomsSmaller = map lessAtomToEdge $ S.toList $ L.get sLessAtoms smaller
  lessRelLarger <- fromSet (S.fromList (rawLessRel larger))
  -- Check that all elements in the smaller relation are contained in the larger
  -- relation.
  guard (all (uncurry (isSmaller lessRelLarger) . apply r) lessAtomsSmaller)
  guard $ runReader (eqStoreInlcusionModR r (L.get sEqStore smaller) (L.get sEqStore larger)) mh
  guard (isEmptySubtermStore $ L.get sSubtermStore smaller)

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

allRenamings :: MaudeHandle -> System -> System -> [Renaming]
allRenamings mh smallerSys largerSys = mapMaybe (runRenaming mh) (allNodeMappings smallerSys largerSys)

isContainedInModRenamingUpTo :: MaudeHandle -> System -> System -> [RenamingUpToWithVars]
isContainedInModRenamingUpTo mh smaller larger =
  mapMaybe (isProgressingAndSubSysUpTo mh smaller larger) (allRenamings mh smaller larger)

getCycleRenamingsOnPath :: ProofContext -> NonEmpty System -> [BackLinkCandidate]
getCycleRenamingsOnPath ctx (leaf:|candidates) = concatMap tryRenaming candidates
  where
    hnd :: MaudeHandle
    hnd = L.get sigmMaudeHandle $ L.get pcSignature ctx

    tryRenaming :: System -> [BackLinkCandidate]
    tryRenaming inner =
      let blEdge = (L.get sId leaf, L.get sId inner)
      in map (fromRenaming blEdge) (isContainedInModRenamingUpTo hnd inner leaf)

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
      guard (length as <= length as')
      return $ (as, as'):l

newtype Or = Any Bool

instance Semigroup Or where
  (Any b1) <> (Any b2) = Any (b1 || b2)

instance Monoid Or where
  mempty = Any False

-- | Tries to rename loops into one another s.t. some of the renamed loops
--   *could* make progress. We early-test whether we could make progress by
--   checking that whether some loop is shorter than the loop it got mapped to.
--   If no loops are provided, we say there are no renamings. Technically, the
--   identity would be a valid renamings, but this renaming will not make
--   progress. We expect that only renamings of loops will progress.
allLoopMappings :: [LoopInstance ColoredNode] -> [LoopInstance ColoredNode] -> [PartialRenaming]
allLoopMappings [] _ = []
allLoopMappings _ [] = []
allLoopMappings lisSml lisLrg =
    map snd
  $ filter (didProgress . fst)
  $ allMappingsGrouped (~>) couldProgress (const True) (Pure idRenaming) (groupF lisSml) (groupF lisLrg)
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

allNodeMappings :: System -> System -> [PartialRenaming]
allNodeMappings smaller larger = do
  (lsSml, spanningSml) <- maybeToList (loopsAndsystemSpanningOrder smaller)
  (lsLrg, spanningLrg) <- maybeToList (loopsAndsystemSpanningOrder larger)
  r0 <- if null lsSml then [Pure idRenaming] else allLoopMappings lsSml lsLrg
  mapAlongEdges nnid (groupByColor getColor) spanningSml spanningLrg (startAt spanningSml) (startAt spanningLrg) r0
  where
    startAt :: TransClosedOrder ColoredNode -> [ColoredNode]
    startAt = S.toList . minima
