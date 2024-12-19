{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}
-- FIXME: better types in checkLevel
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE DeriveAnyClass   #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier & Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Types to represent proofs.
module Theory.Proof (
  -- * Utilities
    LTree(..)
  , mergeMapsWith

  -- * Types
  , ProofStep(..)
  , DiffProofStep(..)
  , Proof
  , DiffProof

  -- ** Paths inside proofs
  , ProofPath
  , atPath
  , atPathDiff
  , modifyAtPath
  , insertPaths
  , insertPathsDiff

  -- ** Folding/modifying proofs
  , mapProofInfo
  , mapDiffProofInfo
  , foldDiffProof
  , annotateProof
  , annotateDiffProof
  , ProofStatus(..)
  , proofStepStatus
  , diffProofStepStatus
  , proofSize
  , annotateProofStatus
  , proofStatus

  -- ** Unfinished proofs
  , sorry
  , unproven
  , diffSorry
  , diffUnproven

  , selectHeuristic
  , selectDiffHeuristic
  , selectTactic
  , selectDiffTactic

  -- ** Incremental proof construction
  , IncrementalProof
  , IncrementalDiffProof
  , Prover
  , DiffProver
  , runProver
  , runDiffProver
  , mapProverProof
  , mapDiffProverDiffProof

  , orelse
  , tryProver
  , sorryProver
  , sorryDiffProver
  , oneStepProver
  , oneStepDiffProver
  , focus
  , focusDiff
  , checkAndExtendProver
  , checkAndExtendDiffProver
  , replaceSorryProver
  , replaceDiffSorryProver

  -- ** Explicit representation of a fully automatic prover
  , SolutionExtractor(..)
  , AutoProver(..)
  , runAutoProver
  , runAutoDiffProver

  -- ** Pretty Printing
  , prettyProof
  , prettyDiffProof
  , prettyProofWith
  , prettyDiffProofWith

  , showProofStatus
  , showDiffProofStatus

  -- ** Parallel Strategy for exploring a proof
  , parLTreeDFS

  -- ** Small-step interface to the constraint solver
  , module Theory.Constraint.Solver

) where

import           GHC.Generics                     (Generic)

import           Data.Binary
import           Data.List
import           Data.List.NonEmpty ( NonEmpty((:|)), (<|) )
import qualified Data.List.NonEmpty               as NE
import qualified Data.Label                       as L
import qualified Data.Map                         as M
import           Data.Maybe
-- import           Data.Monoid

import           Debug.Trace

import           Control.Basics
import           Control.DeepSeq
import qualified Control.Monad.State              as S
import           Control.Parallel.Strategies

import           Theory.Constraint.Solver
import           Theory.Constraint.System.Results
import           Theory.Constraint.System.ID (SystemID)
import           Theory.Model
import           Theory.Proof.Cyclic (CyclicProof(..), toProof, updateFinished, ProofSoundness (Unsound, Sound, Undetermined), soundness)
import           Theory.Text.Pretty
import Utils.Misc (peak)
import Data.Semigroup (Sum (Sum))



------------------------------------------------------------------------------
-- Utility: Trees with uniquely labelled edges.
------------------------------------------------------------------------------

-- | Trees with uniquely labelled edges.
data LTree l a = LNode
     { root     :: a
     , children :: M.Map l (LTree l a)
     }
     deriving( Eq, Ord, Show )

instance Functor (LTree l) where
    fmap f (LNode r cs) = LNode (f r) (M.map (fmap f) cs)

instance Foldable (LTree l) where
    foldMap f (LNode x cs) = f x `mappend` foldMap (foldMap f) cs

instance Traversable (LTree l) where
    traverse f (LNode x cs) = LNode <$> f x <*> traverse (traverse f) cs

-- | A parallel evaluation strategy well-suited for DFS traversal: As soon as
-- a node is forced it sparks off the computation of the number of case-maps
-- of all its children. This way most of the data is already evaulated, when
-- the actual DFS traversal visits it.
--
-- NOT used for now. It sometimes required too much memory.
parLTreeDFS :: Strategy (LTree l a)
parLTreeDFS (LNode x0 cs0) = do
    cs0' <- (`parTraversable` cs0) $ \(LNode x cs) -> LNode x <$> rseq cs
    return $ LNode x0 (M.map (runEval . parLTreeDFS) cs0')

------------------------------------------------------------------------------
-- Utility: Merging maps
------------------------------------------------------------------------------

-- | /O(n+m)/. A generalized union operator for maps with differing types.
mergeMapsWith :: Ord k
              => (a -> c) -> (b -> c) -> (a -> b -> c)
              -> M.Map k a -> M.Map k b -> M.Map k c
mergeMapsWith leftOnly rightOnly combine l r =
    M.map extract $ M.unionWith combine' l' r'
  where
    l' = M.map (Left . Left)  l
    r' = M.map (Left . Right) r

    combine' (Left (Left a)) (Left (Right b)) = Right $ combine a b
    combine' _ _ = error "mergeMapsWith: impossible"

    extract (Left (Left  a)) = leftOnly  a
    extract (Left (Right b)) = rightOnly b
    extract (Right c)        = c


------------------------------------------------------------------------------
-- Proof Steps
------------------------------------------------------------------------------

-- | A proof steps is a proof method together with additional context-dependent
-- information.
data ProofStep a = ProofStep
     { psMethod :: ProofStepMethod
     , psInfo   :: a
     }
     deriving( Eq, Ord, Show, Generic, NFData, Binary )

instance Functor ProofStep where
    fmap f (ProofStep m i) = ProofStep m (f i)

instance Foldable ProofStep where
    foldMap f = f . psInfo

instance Traversable ProofStep where
    traverse f (ProofStep m i) = ProofStep m <$> f i

instance HasFrees a => HasFrees (ProofStep a) where
    foldFrees f (ProofStep m i) = foldFrees f m `mappend` foldFrees f i
    foldFreesOcc  _ _ = const mempty
    mapFrees f (ProofStep m i)  = ProofStep <$> mapFrees f m <*> mapFrees f i

-- | A diff proof steps is a proof method together with additional context-dependent
-- information.
data DiffProofStep a = DiffProofStep
     { dpsMethod :: DiffProofMethod
     , dpsInfo   :: a
     }
     deriving( Eq, Ord, Show, Generic, NFData, Binary )

instance Functor DiffProofStep where
    fmap f (DiffProofStep m i) = DiffProofStep m (f i)

instance Foldable DiffProofStep where
    foldMap f = f . dpsInfo

instance Traversable DiffProofStep where
    traverse f (DiffProofStep m i) = DiffProofStep m <$> f i

instance HasFrees a => HasFrees (DiffProofStep a) where
    foldFrees f (DiffProofStep m i) = foldFrees f m `mappend` foldFrees f i
    foldFreesOcc  _ _ = const mempty
    mapFrees f (DiffProofStep m i)  = DiffProofStep <$> mapFrees f m <*> mapFrees f i


------------------------------------------------------------------------------
-- Proof Trees
------------------------------------------------------------------------------

-- | A path to a subproof.
type ProofPath = [CaseName]

-- | A proof is a tree of proof steps whose edges are labelled with case names.
type Proof a = LTree CaseName (ProofStep a)

-- | A diff proof is a tree of proof steps whose edges are labelled with case names.
type DiffProof a = LTree CaseName (DiffProofStep a)

-- Unfinished proofs
--------------------

resultToProof :: System -> ProofMethod -> ProofMethodResult -> IncrementalProof
resultToProof sys pm pmr = LNode (ProofStep (Left pm) (Just sys)) (M.map mapResult pmr)
  where
    mapResult :: (System, Maybe (Result Contradiction)) -> IncrementalProof
    mapResult (s, Just r) = LNode (ProofStep (Right r) (Just s)) M.empty
    mapResult (s, Nothing) = sorry Nothing (Just s)

-- | A proof using the 'sorry' proof method.
sorry :: Maybe String -> a -> Proof a
sorry reason ann = LNode (ProofStep (Left $ Sorry reason) ann) M.empty

-- | A proof using the 'sorry' proof method.
diffSorry :: Maybe String -> a -> DiffProof a
diffSorry reason ann = LNode (DiffProofStep (DiffSorry reason) ann) M.empty

-- | A proof denoting an unproven part of the proof.
unproven :: a -> Proof a
unproven = sorry Nothing

-- | A proof denoting an unproven part of the proof.
diffUnproven :: a -> DiffProof a
diffUnproven = diffSorry Nothing

-- Paths in proofs
------------------

-- | @prf `atPath` path@ returns the subproof at the @path@ in @prf@.
atPathWith :: Ord l => (a -> b) -> LTree l a -> [l] -> Maybe (LTree l a, NonEmpty b)
atPathWith f n = foldM (uncurry walk) (n, NE.singleton (f (root n)))
  where
    walk p t c = do
      p' <- M.lookup c (children p)
      return (p', f (root p') <| t)

atPath :: IncrementalProof -> ProofPath -> Maybe (IncrementalProof, NonEmpty System)
atPath prf path = do
  (p, sysPath) <- atPathWith psInfo prf path
  return (p, NE.map (fromMaybe $ error "no constraint system") sysPath)

-- | @prf `atPath` path@ returns the subproof at the @path@ in @prf@.
atPathDiff :: IncrementalDiffProof -> ProofPath -> Maybe (IncrementalDiffProof, NonEmpty DiffSystem)
atPathDiff prf path = do
  (p, sysPath) <- atPathWith dpsInfo prf path
  return (p, NE.map (fromMaybe $ error "no constraint system") sysPath)

-- | @modifyAtPath f path prf@ applies @f@ to the subproof at @path@,
-- if there is one.
modifyAtPath :: (NE.NonEmpty System -> IncrementalProof -> Maybe IncrementalProof)
             -> [System] -> ProofPath -> IncrementalProof
             -> Maybe IncrementalProof
modifyAtPath f syssToRoot path p = do
  s <- psInfo $ root p
  go (s :| syssToRoot) path p
  where
    go acc []     prf = f acc prf
    go acc (l:ls) prf = do
        let cs = children prf
        n <- M.lookup l cs
        s <- psInfo $ root n
        prf' <- go (s <| acc) ls n
        return (prf { children = M.insert l prf' cs })

-- | @modifyAtPath f path prf@ applies @f@ to the subproof at @path@,
-- if there is one.
modifyAtPathDiff :: (NonEmpty DiffSystem -> IncrementalDiffProof -> Maybe IncrementalDiffProof) 
                 -> NonEmpty DiffSystem -> ProofPath -> IncrementalDiffProof
                 -> Maybe IncrementalDiffProof
modifyAtPathDiff f =
    go
  where
    go acc []     prf = f acc prf
    go acc (l:ls) prf = do
        let cs = children prf
        n <- M.lookup l cs
        s <- dpsInfo $ root n
        prf' <- go (s <| acc) ls n
        return (prf { children = M.insert l prf' cs })

-- | @insertPaths prf@ inserts the path to every proof node.
insertPaths :: Proof a -> Proof (a, ProofPath)
insertPaths =
    insertPath []
  where
    insertPath path (LNode ps cs) =
        LNode (fmap (,reverse path) ps)
              (M.mapWithKey (\n prf -> insertPath (n:path) prf) cs)

-- | @insertPaths prf@ inserts the path to every diff proof node.
insertPathsDiff :: DiffProof a -> DiffProof (a, ProofPath)
insertPathsDiff =
    insertPath []
  where
    insertPath path (LNode ps cs) =
        LNode (fmap (,reverse path) ps)
              (M.mapWithKey (\n prf -> insertPath (n:path) prf) cs)

-- Utilities for dealing with proofs
------------------------------------


-- | Apply a function to the information of every proof step.
mapProofInfo :: (a -> b) -> Proof a -> Proof b
mapProofInfo = fmap . fmap

-- | Apply a function to the information of every proof step.
mapDiffProofInfo :: (a -> b) -> DiffProof a -> DiffProof b
mapDiffProofInfo = fmap . fmap

-- | @boundProofDepth bound prf@ bounds the depth of the proof @prf@ using
-- 'Sorry' steps to replace the cut sub-proofs.
boundProofDepth :: Int -> Proof a -> Proof a
boundProofDepth bound =
    go bound
  where
    go n (LNode ps@(ProofStep _ info) cs)
      | 0 < n     = LNode ps                     $ M.map (go (pred n)) cs
      | otherwise = sorry (Just $ "bound " ++ show bound ++ " hit") info

-- | @boundProofDepth bound prf@ bounds the depth of the proof @prf@ using
-- 'Sorry' steps to replace the cut sub-proofs.
boundDiffProofDepth :: Int -> DiffProof a -> DiffProof a
boundDiffProofDepth bound =
    go bound
  where
    go n (LNode ps@(DiffProofStep _ info) cs)
      | 0 < n     = LNode ps                     $ M.map (go (pred n)) cs
      | otherwise = diffSorry (Just $ "bound " ++ show bound ++ " hit") info


-- | Fold a proof.
proofSize :: LTree l a -> Sum Integer
proofSize = go
  where
    one = Sum (1 :: Integer)
    go (LNode _ cs) = one <> foldMap go (M.elems cs)

annotateProofStatus :: IncrementalProof -> Proof (Maybe System, ProofStatus)
annotateProofStatus tree =
  let annotated = go tree
  in case snd (psInfo $ root annotated) of
    -- Outermost fmap is for tree, next is for ProofStep, innermost is for tuple
    CompleteProof -> fmap (fmap (fmap setPartialComplete)) annotated
    UnfinishableProof -> setPartialUnfinishable annotated
    _ -> annotated
  where
    go :: IncrementalProof -> Proof (Maybe System, ProofStatus)
    go (LNode s cs)
      | M.null cs = LNode (ftinsert (updateStatus (proofStepStatus s) . fmap (L.get sId)) s) M.empty
      | otherwise =
        let cs' = M.map annotateProofStatus cs
            s' = ftinsert (updateStatus (mconcat (map (snd . psInfo . root) (M.elems cs'))) . fmap (L.get sId)) s
        in  LNode s' cs'

    ftinsert :: Functor f => (a -> b) -> f a -> f (a, b)
    ftinsert f fa = (\a -> (a, f a)) <$> fa

    updateStatus :: ProofStatus -> Maybe SystemID -> ProofStatus
    updateStatus _ Nothing = UndeterminedProof
    updateStatus (PartiallyCompleteProof cp) (Just sid) = case updateFinished sid cp of
      UnsoundProof -> UnfinishableProof
      SoundProof _ -> CompleteProof
      updated@(MaybeSoundProof _ _) -> PartiallyCompleteProof updated
    updateStatus st _ = st

    setPartialComplete :: ProofStatus -> ProofStatus
    setPartialComplete (PartiallyCompleteProof _) = CompleteProof
    setPartialComplete st = st

    setPartialUnfinishable :: Proof (Maybe System, ProofStatus) -> Proof (Maybe System, ProofStatus)
    setPartialUnfinishable t@(LNode step cs) =
      let st = snd $ psInfo step
      in case st of
        CompleteProof -> t
        -- Outermost fmap for ProofStep; innermost is for tuple
        PartiallyCompleteProof _ -> LNode (fmap (fmap (const UnfinishableProof)) step) (M.map setPartialUnfinishable cs)
        _ -> LNode step (M.map setPartialUnfinishable cs)

proofStatus :: IncrementalProof -> ProofStatus
proofStatus = snd . psInfo . root . annotateProofStatus

-- | Fold a proof.
foldDiffProof :: Monoid m => (DiffProofStep a -> m) -> DiffProof a -> m
foldDiffProof f =
    go
  where
    go (LNode step cs) = f step `mappend` foldMap go (M.elems cs)

-- | Annotate a proof in a bottom-up fashion.
annotateProof :: (ProofStep a -> [b] -> b) -> Proof a -> Proof b
annotateProof f =
    go
  where
    go (LNode step@(ProofStep method _) cs) =
        LNode (ProofStep method info') cs'
      where
        cs' = M.map go cs
        info' = f step (map (psInfo . root . snd) (M.toList cs'))

-- | Annotate a proof in a bottom-up fashion.
annotateDiffProof :: (DiffProofStep a -> [b] -> b) -> DiffProof a -> DiffProof b
annotateDiffProof f =
    go
  where
    go (LNode step@(DiffProofStep method _) cs) =
        LNode (DiffProofStep method info') cs'
      where
        cs' = M.map go cs
        info' = f step (map (dpsInfo . root . snd) (M.toList cs'))

-- Proof cutting
----------------

-- | The status of a 'Proof'.
data ProofStatus =
    UndeterminedProof -- ^ At least some steps are unannotated
  | CompleteProof     -- ^ The proof is complete: no annotated sorry,
                      --  no annotated solved step
  | PartiallyCompleteProof CyclicProof
  | IncompleteProof   -- ^ There is a annotated sorry,
                      --   but no annotated solved step.
  | TraceFound        -- ^ There is an annotated solved step
  | UnfinishableProof -- ^ The proof cannot be finished (due to reducible operators in subterms)
                      --   i.e. all ends are either Completed or Unfinishable (if a trace is found, then the status is TraceFound)
  deriving ( Show, Generic, NFData, Binary, Eq )

instance Semigroup ProofStatus where
    TraceFound <> _                        = TraceFound
    _ <> TraceFound                        = TraceFound
    IncompleteProof <> _                   = IncompleteProof
    _ <> IncompleteProof                   = IncompleteProof
    UnfinishableProof <> _                 = UnfinishableProof
    _ <> UnfinishableProof                 = UnfinishableProof
    UndeterminedProof <> _                 = UndeterminedProof
    _ <> UndeterminedProof                 = UndeterminedProof
    CompleteProof <> st                    = st
    st <> CompleteProof                    = st
    PartiallyCompleteProof cp <> PartiallyCompleteProof cp' = PartiallyCompleteProof (cp <> cp')

instance Monoid ProofStatus where
    mempty = CompleteProof

-- | The status of a 'ProofStep'.
proofStepStatus :: ProofStep (Maybe a) -> ProofStatus
proofStepStatus (ProofStep _ Nothing) = UndeterminedProof
proofStepStatus (ProofStep (Right Solved) (Just _)) = TraceFound
proofStepStatus (ProofStep (Right Unfinishable) (Just _)) = UnfinishableProof
proofStepStatus (ProofStep (Left (Sorry _)) (Just _)) = IncompleteProof
proofStepStatus (ProofStep (Right (Contradictory (Just (Cyclic bl)))) (Just _)) =
  PartiallyCompleteProof (toProof bl)
proofStepStatus (ProofStep _ (Just _)) = CompleteProof

-- | The status of a 'DiffProofStep'.
diffProofStepStatus :: DiffProofStep (Maybe a) -> ProofStatus
diffProofStepStatus (DiffProofStep _                Nothing ) = UndeterminedProof
diffProofStepStatus (DiffProofStep DiffAttack       (Just _)) = TraceFound
diffProofStepStatus (DiffProofStep (DiffSorry _)    (Just _)) = IncompleteProof
diffProofStepStatus (DiffProofStep DiffUnfinishable (Just _)) = UnfinishableProof
diffProofStepStatus (DiffProofStep _                (Just _)) = CompleteProof

-- | @checkProof rules se prf@ replays the proof @prf@ against the start
-- sequent @se@. A failure to apply a proof method is denoted by a resulting
-- proof step without an annotated sequent. An unhandled case is denoted using
-- the 'Sorry' proof method.
checkProof :: ProofContext
           -> (Int -> NonEmpty System -> Proof (Maybe System)) -- prover for new cases in depth
           -> Int
           -> NonEmpty System
           -> Proof a
           -> Proof (Maybe a, Maybe System)
checkProof ctxt prover =
    go
  where
    noSystemPrf = mapProofInfo (\i -> (Just i, Nothing))
    node m info sys = LNode (ProofStep m (Just info, Just sys))
    sorryNode reason cases info sys = node (Left $ Sorry reason) info sys (M.map noSystemPrf cases)
    invalidProofStep prf = sorryNode (Just "invalid proof step encountered")
      (M.singleton "" prf)

    go _ syss@(sys:|_) prf@(LNode (ProofStep m@(Right result) info) _)
      | maybe False (equivResult result) (isFinished ctxt syss) = node m info sys M.empty
      | otherwise = invalidProofStep prf info sys
    go d syss@(sys:|_) prf@(LNode (ProofStep m@(Left method) info) cs) = case (method, checkAndExecProofMethod ctxt method syss) of
      (Sorry reason, _         ) -> sorryNode reason cs info sys
      (_           , Just cases) -> node m info sys $ checkChildren $ M.map ((<| syss) . fst) cases  -- TODO:
      (_           , Nothing   ) -> invalidProofStep prf info sys
      where
        unhandledCase = mapProofInfo (Nothing,) . prover d
        checkChildren cases = mergeMapsWith unhandledCase noSystemPrf (go (d + 1)) cases cs


-- | @checkDiffProof rules se prf@ replays the proof @prf@ against the start
-- sequent @se@. A failure to apply a proof method is denoted by a resulting
-- proof step without an annotated sequent. An unhandled case is denoted using
-- the 'Sorry' proof method.
checkDiffProof :: DiffProofContext
           -> (Int -> NonEmpty DiffSystem -> DiffProof (Maybe DiffSystem)) -- prover for new cases in depth
           -> Int
           -> NonEmpty DiffSystem
           -> DiffProof a
           -> DiffProof (Maybe a, Maybe DiffSystem)
checkDiffProof ctxt prover =
    go
  where
    go d syss@(s:|_) prf@(LNode (DiffProofStep method info) cs) = case (method, execDiffProofMethod ctxt method syss) of
      (DiffSorry reason, _         ) -> sorryNode reason cs
      (_               , Just cases) -> node method $ checkChildren $ M.map (<| syss) cases
      (_               , Nothing   ) ->
          sorryNode (Just "invalid proof step encountered")
                    (M.singleton "" prf)
      where
        unhandledCase = mapDiffProofInfo (Nothing,) . prover d
        checkChildren cases = mergeMapsWith unhandledCase noSystemPrf (go (d + 1)) cases cs

        node m                 = LNode (DiffProofStep m (Just info, Just s))
        sorryNode reason cases = node (DiffSorry reason) (M.map noSystemPrf cases)
        noSystemPrf            = mapDiffProofInfo (\i -> (Just i, Nothing))

------------------------------------------------------------------------------
-- Provers: the interface to the outside world.
------------------------------------------------------------------------------

-- | Incremental proofs are used to represent intermediate results of proof
-- checking/construction.
type IncrementalProof = Proof (Maybe System)

-- | Incremental diff proofs are used to represent intermediate results of proof
-- checking/construction.
type IncrementalDiffProof = DiffProof (Maybe DiffSystem)


-- | Provers whose sequencing is handled via the 'Monoid' instance.
--
-- > p1 `mappend` p2
--
-- Is a prover that first runs p1 and then p2 on the resulting proof.
newtype Prover =  Prover
          { runProver
              :: ProofContext              -- proof rules to use
              -> Int                       -- proof depth
              -> NonEmpty System           -- path of sequents to start with
              -> IncrementalProof          -- original proof
              -> Maybe IncrementalProof    -- resulting proof
          }

instance Semigroup Prover where
    p1 <> p2 = Prover $ \ctxt d se ->
        runProver p1 ctxt d se >=> runProver p2 ctxt d se

instance Monoid Prover where
    mempty          = Prover $ \_  _ _ -> Just

-- | Provers whose sequencing is handled via the 'Monoid' instance.
--
-- > p1 `mappend` p2
--
-- Is a prover that first runs p1 and then p2 on the resulting proof.
newtype DiffProver =  DiffProver
          { runDiffProver
              :: DiffProofContext              -- proof rules to use
              -> Int                           -- proof depth
              -> NonEmpty DiffSystem           -- path of sequents to start with
              -> IncrementalDiffProof          -- original proof
              -> Maybe IncrementalDiffProof    -- resulting proof
          }

instance Semigroup DiffProver where
    p1 <> p2 = DiffProver $ \ctxt d se ->
        runDiffProver p1 ctxt d se >=> runDiffProver p2 ctxt d se

instance Monoid DiffProver where
    mempty          = DiffProver $ \_  _ _ -> Just

-- | Map the proof generated by the prover.
mapProverProof :: (IncrementalProof -> IncrementalProof) -> Prover -> Prover
mapProverProof f p = Prover $ \ ctxt d se prf -> f <$> runProver p ctxt d se prf

-- | Map the proof generated by the prover.
mapDiffProverDiffProof :: (IncrementalDiffProof -> IncrementalDiffProof) -> DiffProver -> DiffProver
mapDiffProverDiffProof f p = DiffProver $ \ctxt d se prf -> f <$> runDiffProver p ctxt d se prf

-- | Resorts to the second prover, if the first one is not successful.
orelse :: Prover -> Prover -> Prover
orelse p1 p2 = Prover $ \ctxt d syss prf ->
    runProver p1 ctxt d syss prf `mplus` runProver p2 ctxt d syss prf

-- | Try to apply a prover. If it fails, just return the original proof.
tryProver :: Prover -> Prover
tryProver =  (`orelse` mempty)

-- TODO: Rewrite caller of this function so that I don't need to check the proof method
-- | Try to execute one proof step using the given proof method.
oneStepProver :: ProofMethod -> Prover
oneStepProver method = Prover $ \ctxt _ syss@(sys:|_) _ -> do
    res <- checkAndExecProofMethod ctxt method syss
    return $ resultToProof sys method res

-- | Try to execute one proof step using the given proof method.
oneStepDiffProver :: DiffProofMethod -> DiffProver
oneStepDiffProver method = DiffProver $ \ctxt _ syss@(sys:|_) _ -> do
    cases <- execDiffProofMethod ctxt method syss
    return $ LNode (DiffProofStep method (Just sys)) (M.map (diffUnproven . Just) cases)

-- | Replace the current proof with a sorry step and the given reason.
sorryProver :: Maybe String -> Prover
sorryProver reason = Prover $ \_ _ (sys:|_) _ -> return $ sorry reason (Just sys)

-- | Replace the current proof with a sorry step and the given reason.
sorryDiffProver :: Maybe String -> DiffProver
sorryDiffProver reason = DiffProver $ \_ _ (sys:|_) _ -> return $ diffSorry reason (Just sys)

-- | Apply a prover only to a sub-proof, fails if the subproof doesn't exist.
focus :: ProofPath -> Prover -> Prover
focus []   prover = prover
focus path prover = Prover $ \ctxt d (_:|t) prf ->
  modifyAtPath (runProver prover ctxt (d + length path)) t path prf

-- | Apply a diff prover only to a sub-proof, fails if the subproof doesn't exist.
focusDiff :: ProofPath -> DiffProver -> DiffProver
focusDiff []   prover = prover
focusDiff path prover =
    DiffProver $ \ctxt d syss prf ->
        modifyAtPathDiff (prover' ctxt (d + length path)) syss path prf
  where
    prover' ctxt d syss prf = do
        se <- dpsInfo (root prf)
        runDiffProver prover ctxt d (se <| syss) prf

-- | Check the proof and handle new cases using the given prover.
checkAndExtendProver :: Prover -> Prover
checkAndExtendProver prover0 = Prover $ \ctxt d syss prf ->
    return $ mapProofInfo snd $ checkProof ctxt (prover ctxt) d syss prf
  where
    unhandledCase   = sorry (Just "unhandled case") Nothing
    prover ctxt d se =
        fromMaybe unhandledCase $ runProver prover0 ctxt d se unhandledCase

-- | Check the proof and handle new cases using the given prover.
checkAndExtendDiffProver :: DiffProver -> DiffProver
checkAndExtendDiffProver prover0 = DiffProver $ \ctxt d se prf ->
    return $ mapDiffProofInfo snd $ checkDiffProof ctxt (prover ctxt) d se prf
  where
    unhandledCase = diffSorry (Just "unhandled case") Nothing
    prover ctxt d se =
        fromMaybe unhandledCase $ runDiffProver prover0 ctxt d se unhandledCase

-- | Replace all annotated sorry steps using the given prover.
replaceSorryProver :: Prover -> Prover
replaceSorryProver prover0 = Prover prover
  where
    prover ctxt d path = return . replace path
      where
        replace sysPath prf@(LNode (ProofStep (Left (Sorry _)) (Just se)) _) =
          fromMaybe prf $ runProver prover0 ctxt d (se <| sysPath) prf
        replace sysPath (LNode ps cases) = LNode ps (M.map mapNode cases)
          where
            mapNode n = replace (fromMaybe (error "missing constraint system") (psInfo $ root n) <| sysPath) n

-- | Replace all annotated sorry steps using the given prover.
replaceDiffSorryProver :: DiffProver -> DiffProver
replaceDiffSorryProver prover0 = DiffProver prover
  where
    prover ctxt d path = return . replace path
      where
        replace sysPath prf@(LNode (DiffProofStep (DiffSorry _) (Just se)) _) =
            fromMaybe prf $ runDiffProver prover0 ctxt d (se <| sysPath) prf
        replace sysPath (LNode ps cases) =
          LNode ps $ M.map mapNode cases
          where
            mapNode n = fromMaybe n $ do
              s <- dpsInfo $ root n
              return $ replace (s <| sysPath) n

------------------------------------------------------------------------------
-- Automatic Prover's
------------------------------------------------------------------------------

data SolutionExtractor = CutDFS | CutBFS | CutSingleThreadDFS | CutNothing | CutAfterSorry
    deriving( Eq, Ord, Show, Read, Generic, NFData, Binary )

data AutoProver = AutoProver
    { apDefaultHeuristic :: Maybe (Heuristic ProofContext)
    , apDefaultTactic   :: Maybe [Tactic ProofContext]
    , apBound            :: Maybe Int
    , apCut              :: SolutionExtractor
    , quitOnEmptyOracle  :: Bool
    }
    deriving ( Generic, NFData, Binary )

selectHeuristic :: AutoProver -> ProofContext -> Heuristic ProofContext
selectHeuristic prover ctx = setQuitOnEmpty $ fromMaybe (defaultHeuristic False)
                             (apDefaultHeuristic prover <|> L.get pcHeuristic ctx)
  where
    setQuitOnEmpty :: Heuristic ProofContext -> Heuristic ProofContext
    setQuitOnEmpty (Heuristic rankings) = Heuristic (map aux rankings)

    aux :: GoalRanking a -> GoalRanking a
    aux (OracleRanking _ o) = OracleRanking (quitOnEmptyOracle prover) o
    aux (OracleSmartRanking _ o) = OracleSmartRanking (quitOnEmptyOracle prover) o
    aux (InternalTacticRanking _ t) = InternalTacticRanking (quitOnEmptyOracle prover) t
    aux gr = gr

selectDiffHeuristic :: AutoProver -> DiffProofContext -> Heuristic ProofContext
selectDiffHeuristic prover ctx = fromMaybe (defaultHeuristic True)
                                 (apDefaultHeuristic prover <|> L.get pcHeuristic (L.get dpcPCLeft ctx))

selectTactic :: AutoProver -> ProofContext -> [Tactic ProofContext]
selectTactic prover ctx = fromMaybe [defaultTactic]
                             (apDefaultTactic prover <|> L.get pcTactic ctx)

selectDiffTactic :: AutoProver -> DiffProofContext -> [Tactic ProofContext]
selectDiffTactic prover ctx = fromMaybe [defaultTactic]
                                 (apDefaultTactic prover <|> L.get pcTactic (L.get dpcPCLeft ctx))

runAutoProver :: AutoProver -> Prover
runAutoProver aut@(AutoProver _ _  bound cut _) =
    mapProverProof cutSolved $ maybe id boundProver bound autoProver
  where
    cutSolved = case cut of
      CutDFS             -> cutOnSolvedDFS
      CutBFS             -> cutOnSolvedBFS
      CutSingleThreadDFS -> cutOnSolvedSingleThreadDFS
      CutNothing         -> id
      CutAfterSorry      -> cutAfterFirstSorry

    -- | The standard automatic prover that ignores the existing proof and
    -- tries to find one by itself.
    autoProver :: Prover
    autoProver = Prover $ \ctxt depth sysPath _ ->
        return $ proveSystemDFS (selectHeuristic aut ctxt) (selectTactic aut ctxt) ctxt depth sysPath

    -- | Bound the depth of proofs generated by the given prover.
    boundProver :: Int -> Prover -> Prover
    boundProver b p = Prover $ \ctxt d syss prf ->
        boundProofDepth b <$> runProver p ctxt d syss prf

runAutoDiffProver :: AutoProver -> DiffProver
runAutoDiffProver aut@(AutoProver _ _ bound cut _) =
    mapDiffProverDiffProof cutSolved $ maybe id boundProver bound autoProver
  where
    cutSolved = case cut of
      CutDFS             -> cutOnSolvedDFSDiff
      CutBFS             -> cutOnSolvedBFSDiff
      CutSingleThreadDFS -> cutOnSolvedSingleThreadDFSDiff
      CutAfterSorry      -> cutAfterFirstSorryDiff
      CutNothing         -> id

    -- | The standard automatic prover that ignores the existing proof and
    -- tries to find one by itself.
    autoProver :: DiffProver
    autoProver = DiffProver $ \ctxt depth syss _ ->
        return $ proveDiffSystemDFS (selectDiffHeuristic aut ctxt) (selectDiffTactic aut ctxt) ctxt depth syss

    -- | Bound the depth of proofs generated by the given prover.
    boundProver :: Int -> DiffProver -> DiffProver
    boundProver b p = DiffProver $ \ctxt d se prf ->
        boundDiffProofDepth b <$> runDiffProver p ctxt d se prf


-- | The result of one pass of iterative deepening.
data IterDeepRes = NoSolution | MaybeNoSolution | Solution ProofPath

instance Semigroup IterDeepRes where
    x@(Solution _)   <> _                = x
    _                <> y@(Solution _)   = y
    MaybeNoSolution  <> _                = MaybeNoSolution
    _                <> MaybeNoSolution  = MaybeNoSolution
    NoSolution       <> NoSolution       = NoSolution

instance Monoid IterDeepRes where
    mempty = NoSolution

-- | @cutOnSolvedSingleThreadDFS prf@ removes all other cases if an attack is
-- found. The attack search is performed using a single-thread DFS traversal.
--
-- FIXME: Note that this function may use a lot of space, as it holds onto the
-- whole proof tree.
cutOnSolvedSingleThreadDFS :: Proof (Maybe a) -> Proof (Maybe a)
cutOnSolvedSingleThreadDFS prf0 =
    go $ insertPaths prf0
  where
    go prf = case findSolved prf of
        NoSolution      -> prf0
        Solution path   -> extractSolved path prf0
        MaybeNoSolution -> error "Theory.Constraint.cutOnSolvedSingleThreadDFS: impossible, MaybeNoSolution in single thread dfs"
      where
        findSolved node = case node of
              -- do not search in nodes that are not annotated
              LNode (ProofStep _              (Nothing, _   )) _  -> NoSolution
              LNode (ProofStep (Right Solved) (Just _ , path)) _  -> Solution path
              LNode (ProofStep _              (Just _ , _   )) cs ->
                  foldMap findSolved cs

    extractSolved []         p               = p
    extractSolved (label:ps) (LNode pstep m) = case M.lookup label m of
        Just subprf ->
          LNode pstep (M.fromList [(label, extractSolved ps subprf)])
        Nothing     ->
          error "Theory.Constraint.cutOnSolvedSingleThreadDFS: impossible, extractSolved failed, invalid path"

-- | @cutOnSolvedSingleThreadDFSDiffDFS prf@ removes all other cases if an
-- attack is found. The attack search is performed using a single-thread DFS
-- traversal.
--
-- FIXME: Note that this function may use a lot of space, as it holds onto the
-- whole proof tree.
cutOnSolvedSingleThreadDFSDiff :: DiffProof (Maybe a) -> DiffProof (Maybe a)
cutOnSolvedSingleThreadDFSDiff prf0 =
    go $ insertPathsDiff prf0
  where
    go prf = case findSolved prf of
        NoSolution      -> prf0
        Solution path   -> extractSolved path prf0
        MaybeNoSolution -> error "Theory.Constraint.cutOnSolvedSingleThreadDFSDiff: impossible, MaybeNoSolution in single thread dfs"
      where
        findSolved node = case node of
              -- do not search in nodes that are not annotated
              LNode (DiffProofStep _      (Nothing, _   )) _  -> NoSolution
              LNode (DiffProofStep DiffAttack (Just _ , path)) _  -> Solution path
              LNode (DiffProofStep _      (Just _ , _   )) cs ->
                  foldMap findSolved cs

    extractSolved []         p               = p
    extractSolved (label:ps) (LNode pstep m) = case M.lookup label m of
        Just subprf ->
          LNode pstep (M.fromList [(label, extractSolved ps subprf)])
        Nothing     ->
          error "Theory.Constraint.cutOnSolvedSingleThreadDFSDiff: impossible, extractSolved failed, invalid path"

-- | @cutOnSolvedDFS prf@ removes all other cases if an attack is found. The
-- attack search is performed using a parallel DFS traversal with iterative
-- deepening.
-- Note that when an attack is found, other, already started threads will not be
-- stopped. They will first run to completion, and only afterwards will the proof
-- complete. If this is undesirable bahavior, use cutOnSolvedSingleThreadDFS.
--
-- FIXME: Note that this function may use a lot of space, as it holds onto the
-- whole proof tree.
cutOnSolvedDFS :: Proof (Maybe a) -> Proof (Maybe a)
cutOnSolvedDFS prf0 =
    go (4 :: Integer) $ insertPaths prf0
  where
    go dMax prf = case findSolved 0 prf of
        NoSolution      -> prf0
        MaybeNoSolution -> go (2 * dMax) prf
        Solution path   -> extractSolved path prf0
      where
        findSolved d node
          | d >= dMax = MaybeNoSolution
          | otherwise = case node of
              -- do not search in nodes that are not annotated
              LNode (ProofStep _              (Nothing, _   )) _  -> NoSolution
              LNode (ProofStep (Right Solved) (Just _ , path)) _  -> Solution path
              LNode (ProofStep _              (Just _ , _   )) cs ->
                  foldMap (findSolved (succ d))
                      (cs `using` parTraversable nfProofMethod)

        nfProofMethod node = do
            void $ rseq (psMethod $ root node)
            void $ rseq (psInfo   $ root node)
            void $ rseq (children node)
            return node

    extractSolved []         p               = p
    extractSolved (label:ps) (LNode pstep m) = case M.lookup label m of
        Just subprf ->
          LNode pstep (M.fromList [(label, extractSolved ps subprf)])
        Nothing     ->
          error "Theory.Constraint.cutOnSolvedDFS: impossible, extractSolved failed, invalid path"

-- | @cutOnSolvedDFSDiff prf@ removes all other cases if an attack is found. The
-- attack search is performed using a parallel DFS traversal with iterative
-- deepening.
-- Note that when an attack is found, other, already started threads will not be
-- stopped. They will first run to completion, and only afterwards will the proof
-- complete. If this is undesirable bahavior, use cutOnSolvedSingleThreadDFSDiff.
--
-- FIXME: Note that this function may use a lot of space, as it holds onto the
-- whole proof tree.
cutOnSolvedDFSDiff :: DiffProof (Maybe a) -> DiffProof (Maybe a)
cutOnSolvedDFSDiff prf0 =
    go (4 :: Integer) $ insertPathsDiff prf0
  where
    go dMax prf = case findSolved 0 prf of
        NoSolution      -> prf0
        MaybeNoSolution -> go (2 * dMax) prf
        Solution path   -> extractSolved path prf0
      where
        findSolved d node
          | d >= dMax = MaybeNoSolution
          | otherwise = case node of
              -- do not search in nodes that are not annotated
              LNode (DiffProofStep _          (Nothing, _   )) _  -> NoSolution
              LNode (DiffProofStep DiffAttack (Just _ , path)) _  -> Solution path
              LNode (DiffProofStep _          (Just _ , _   )) cs ->
                  foldMap (findSolved (succ d))
                      (cs `using` parTraversable nfProofMethod)

        nfProofMethod node = do
            void $ rseq (dpsMethod $ root node)
            void $ rseq (dpsInfo   $ root node)
            void $ rseq (children node)
            return node

    extractSolved []         p               = p
    extractSolved (label:ps) (LNode pstep m) = case M.lookup label m of
        Just subprf ->
          LNode pstep (M.fromList [(label, extractSolved ps subprf)])
        Nothing     ->
          error "Theory.Constraint.cutOnSolvedDFSDiff: impossible, extractSolved failed, invalid path"

-- | Search for attacks in a BFS manner.
cutOnSolvedBFS :: Proof (Maybe a) -> Proof (Maybe a)
cutOnSolvedBFS =
    go (1::Int)
  where
    go l prf =
      -- FIXME: See if that poor man's logging could be done better.
      trace ("searching for attacks at depth: " ++ show l) $
        case S.runState (checkLevel l prf) CompleteProof of
          (_, UndeterminedProof) -> error "cutOnSolvedBFS: impossible"
          (_, CompleteProof)     -> prf
          (_, UnfinishableProof) -> prf
          (_, PartiallyCompleteProof _) -> go (l+1) prf
          (_, IncompleteProof)   -> go (l+1) prf
          (prf', TraceFound)     ->
              trace ("attack found at depth: " ++ show l) prf'

    checkLevel 0 (LNode  step@(ProofStep (Right Solved) (Just _)) _) =
        S.put TraceFound >> return (LNode step M.empty)
    checkLevel 0 prf@(LNode (ProofStep _ x) cs)
      | M.null cs = return prf
      | otherwise = do
          st <- S.get
          msg <- case st of
              TraceFound -> return $ "ignored (attack exists)"
              _           -> S.put IncompleteProof >> return "bound reached"
          return $ LNode (ProofStep (Left (Sorry (Just msg))) x) M.empty
    checkLevel l prf@(LNode step cs)
      | isNothing (psInfo step) = return prf
      | otherwise               = LNode step <$> traverse (checkLevel (l-1)) cs

-- | Search for attacks in a BFS manner.
cutOnSolvedBFSDiff :: DiffProof (Maybe a) -> DiffProof (Maybe a)
cutOnSolvedBFSDiff =
    go (1::Int)
  where
    go l prf =
      -- FIXME: See if that poor man's logging could be done better.
      trace ("searching for attacks at depth: " ++ show l) $
        case S.runState (checkLevel l prf) CompleteProof of
          (_, UndeterminedProof) -> error "cutOnSolvedBFS: impossible"
          (_, PartiallyCompleteProof _) -> error "cyclic proofs are not supported in diff mode"
          (_, CompleteProof)     -> prf
          (_, UnfinishableProof) -> prf
          (_, IncompleteProof)   -> go (l+1) prf
          (prf', TraceFound)     ->
              trace ("attack found at depth: " ++ show l) prf'

    checkLevel 0 (LNode  step@(DiffProofStep DiffAttack (Just _)) _) =
        S.put TraceFound >> return (LNode step M.empty)
    checkLevel 0 prf@(LNode (DiffProofStep _ x) cs)
      | M.null cs = return prf
      | otherwise = do
          st <- S.get
          msg <- case st of
              TraceFound -> return $ "ignored (attack exists)"
              _           -> S.put IncompleteProof >> return "bound reached"
          return $ LNode (DiffProofStep (DiffSorry (Just msg)) x) M.empty
    checkLevel l prf@(LNode step cs)
      | isNothing (dpsInfo step) = return prf
      | otherwise                = LNode step <$> traverse (checkLevel (l-1)) cs

cutAfterFirstSorry :: Proof (Maybe a) -> Proof (Maybe a)
cutAfterFirstSorry = snd . go False
  where
    go :: Bool -> Proof (Maybe a) -> (Bool, Proof (Maybe a))
    go _      n@(LNode (ProofStep (Left (Sorry _)) _) _)     = (True, n)
    go abort  n@(LNode (ProofStep (Right _) _) _)  = (abort, n)
    go True     (LNode (ProofStep _ ann) _)           = (True, LNode (ProofStep (Left (Sorry Nothing)) ann) M.empty)
    go False    (LNode r cs) =
      let (abort, cs') = M.mapAccum go False cs
      in (abort, LNode r cs')


cutAfterFirstSorryDiff :: DiffProof (Maybe a) -> DiffProof (Maybe a)
cutAfterFirstSorryDiff = snd . go False
  where
    go :: Bool -> DiffProof (Maybe a) -> (Bool, DiffProof (Maybe a))
    go _      n@(LNode (DiffProofStep (DiffSorry _) _) _)     = (True, n)
    go abort  n@(LNode (DiffProofStep DiffMirrored _) _)      = (abort, n)
    go abort  n@(LNode (DiffProofStep DiffUnfinishable _) _)  = (abort, n)
    go abort  n@(LNode (DiffProofStep DiffAttack _) _)        = (abort, n)
    go True     (LNode (DiffProofStep _ ann) _)               = (True, LNode (DiffProofStep (DiffSorry Nothing) ann) M.empty)
    go False    (LNode r cs) =
      let (abort, cs') = M.mapAccum go False cs
      in (abort, LNode r cs')

-- | @proveSystemDFS rules se@ explores all solutions of the initial
-- constraint system using a depth-first-search strategy to resolve the
-- non-determinism wrt. what goal to solve next.  This proof can be of
-- infinite depth, if the proof strategy loops.
proveSystemDFS :: Heuristic ProofContext -> [Tactic ProofContext] -> ProofContext -> Int -> NonEmpty System -> IncrementalProof
proveSystemDFS heuristic tactics ctxt = prove
  where
    prove !depth syss@(sys:|_) = fromMaybe failProof $ do
      (method, (r, _)) <- peak (execRankedProofMethods (useHeuristic heuristic depth) tactics ctxt syss)
      let nextLevel = resultToProof sys method r
      return $ mapChildren nextLevel
      where
        mapChild :: IncrementalProof -> IncrementalProof
        mapChild (LNode (ProofStep (Left _) ann) _) = fromMaybe failProof $ do
          s <- ann
          return $ prove (depth + 1) (s <| syss)
        mapChild n@(LNode (ProofStep (Right _) _) _) = n -- Stop recursion on contradictions

        mapChildren :: IncrementalProof -> IncrementalProof
        mapChildren (LNode ann cs) = LNode ann (M.map mapChild cs)

        failProof :: IncrementalProof
        failProof = resultToProof sys (Sorry (Just "neither result nor proof methods")) M.empty

-- | @proveSystemDFS rules se@ explores all solutions of the initial
-- constraint system using a depth-first-search strategy to resolve the
-- non-determinism wrt. what goal to solve next.  This proof can be of
-- infinite depth, if the proof strategy loops.
proveDiffSystemDFS :: Heuristic ProofContext -> [Tactic ProofContext] -> DiffProofContext -> Int -> NonEmpty DiffSystem -> DiffProof (Maybe DiffSystem)
proveDiffSystemDFS heuristic tactics ctxt =
    prove
  where
    prove !depth syss@(sys:|_) =
        case rankDiffProofMethods (useHeuristic heuristic depth) tactics ctxt syss of
          []                         -> node (DiffSorry (Just "Cannot prove")) M.empty
          (method, (cases, _expl)):_ -> node method cases
      where
        node method cases =
          LNode (DiffProofStep method (Just sys)) (M.map (prove (succ depth) . (<| syss)) cases)

------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------


prettyProof :: HighlightDocument d => Proof a -> d
prettyProof = prettyProofWith (either prettyProofMethod prettyResult . psMethod) (const id)

prettyProofWith :: HighlightDocument d
                => (ProofStep a -> d)      -- ^ Make proof step pretty
                -> (ProofStep a -> d -> d) -- ^ Make whole case pretty
                -> Proof a                 -- ^ The proof to prettify
                -> d
prettyProofWith prettyStep prettyCase =
    ppPrf
  where
    ppPrf (LNode ps cs) = ppCases ps (M.toList cs)

    ppCases ps@(ProofStep (Right Solved) _) [] = prettyStep ps
    ppCases ps []                      = prettyCase ps (kwBy <> text " ")
                                           <> prettyStep ps
    ppCases ps [("", prf)]             = prettyStep ps $-$ ppPrf prf
    ppCases ps cases                   =
        prettyStep ps $-$
        (vcat $ intersperse (prettyCase ps kwNext) $ map ppCase cases) $-$
        prettyCase ps kwQED

    ppCase (name, prf) = nest 2 $
      (prettyCase (root prf) $ kwCase <-> text name) $-$
      ppPrf prf

prettyDiffProof :: HighlightDocument d => DiffProof a -> d
prettyDiffProof = prettyDiffProofWith (prettyDiffProofMethod . dpsMethod) (const id)

prettyDiffProofWith :: HighlightDocument d
                => (DiffProofStep a -> d)      -- ^ Make proof step pretty
                -> (DiffProofStep a -> d -> d) -- ^ Make whole case pretty
                -> DiffProof a                 -- ^ The proof to prettify
                -> d
prettyDiffProofWith prettyStep prettyCase =
    ppPrf
  where
    ppPrf (LNode ps cs) = ppCases ps (M.toList cs)

    ppCases ps@(DiffProofStep DiffMirrored _) [] = prettyStep ps
    ppCases ps []                              = prettyCase ps (kwBy <> text " ")
                                                  <> prettyStep ps
    ppCases ps [("", prf)]                     = prettyStep ps $-$ ppPrf prf
    ppCases ps cases                           =
        prettyStep ps $-$
        (vcat $ intersperse (prettyCase ps kwNext) $ map ppCase cases) $-$
        prettyCase ps kwQED

    ppCase (name, prf) = nest 2 $
      (prettyCase (root prf) $ kwCase <-> text name) $-$
      ppPrf prf

-- | Convert a proof status to a readable string.
showProofStatus :: SystemTraceQuantifier -> ProofStatus -> String
showProofStatus ExistsNoTrace   TraceFound        = "falsified - found trace"
showProofStatus ExistsNoTrace   CompleteProof     = "verified"
showProofStatus ExistsSomeTrace CompleteProof     = "falsified - no trace found"
showProofStatus ExistsSomeTrace TraceFound        = "verified"
showProofStatus _               UnfinishableProof = "analysis cannot be finished (reducible operators in subterms)"
showProofStatus _               IncompleteProof   = "analysis incomplete"
showProofStatus _               UndeterminedProof = "analysis undetermined"
-- TODO: Not sure if this is all I need
showProofStatus _               (PartiallyCompleteProof p) = case soundness p of
  Unsound -> "unsound cyclic proof"
  Sound -> "finished cyclic proof"
  Undetermined -> "ongoing cyclic proof"

-- | Convert a proof status to a readable string.
showDiffProofStatus :: ProofStatus -> String
showDiffProofStatus TraceFound        = "falsified - found trace"
showDiffProofStatus CompleteProof     = "verified"
showDiffProofStatus UnfinishableProof = "analysis cannot be finished (reducible operators in subterms)"
showDiffProofStatus IncompleteProof   = "analysis incomplete"
showDiffProofStatus UndeterminedProof = "analysis undetermined"
showDiffProofStatus (PartiallyCompleteProof _) = error "cyclic proofs are not supported in diff mode"

-- Instances
--------------------
instance (Ord l, NFData l, NFData a) => NFData (LTree l a) where
  rnf (LNode r m) = rnf r `seq` rnf  m

instance (Ord l, Binary l, Binary a) => Binary (LTree l a) where
  put (LNode r m) = put r >> put m
  get = LNode <$> get <*> get
