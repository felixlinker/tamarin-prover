{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE ViewPatterns     #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- The constraint reduction rules, which are not enforced as invariants in
-- "Theory.Constraint.Solver.Reduction".
--
-- A goal represents a possible application of a rule that may result in
-- multiple cases or even non-termination (if applied repeatedly). These goals
-- are computed as the list of 'annotateGoals'. See
-- "Theory.Constraint.Solver.ProofMethod" for the public interface to solving
-- goals and the implementation of heuristics.
module Theory.Constraint.Solver.Goals
  ( isSolved
  , annotateGoals
  , solveGoal
  , plainOpenGoals
  , insertCyclicGoals
  ) where

import           Prelude                                 hiding (id, (.))

import qualified Data.ByteString.Char8                   as BC
import qualified Data.DAG.Simple                         as D (reachableSet)
-- import           Data.Foldable                           (foldMap)
import qualified Data.Map                                as M
import qualified Data.Monoid                             as Mono
import qualified Data.Set                                as S
import qualified Data.List.NonEmpty as NE

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.State                     (gets)
import qualified Control.Monad.State as St

import           Extension.Data.Label                    as L

import           Theory.Constraint.Solver.Contradictions (substCreatesNonNormalTerms)
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.System
import           Theory.Tools.IntruderRules (mkDUnionRule, isDExpRule, isDPMultRule, isDEMapRule)
import           Theory.Model
import           Term.Builtin.Convenience


import Utils.Misc (twoPartitions, peakTail, splitBetween)
import Data.Maybe (isNothing, catMaybes, isJust, fromJust)
import Theory.Constraint.System.Inclusion (getCycleRenamingOnPath, BackLinkCandidate (PartialCyclicProof))
import Data.List.NonEmpty as NE (NonEmpty((:|)))
import Utils.PartialOrd (TransClosedOrder(..), fromSet, getLarger, getDirectlyLarger)
import Data.Tuple (swap)
import Control.Monad.RWS (MonadReader(ask), MonadWriter (tell))
import Theory.Constraint.System.Results (Result(Contradictory), Contradiction (Cyclic))
import Data.Bool (bool)

------------------------------------------------------------------------------
-- Extracting Goals
------------------------------------------------------------------------------

-- Instances
------------

isRedundant :: System -> Goal -> Bool
isRedundant se (SplitG idx) = not (splitExists (get sEqStore se) idx)
isRedundant se (SubtermG st) = st `notElem` L.get (posSubterms . sSubtermStore) se
isRedundant _ (DisjG (Disj [])) = True
isRedundant se (ActionG i (Fact KUFact _ _ [m])) =
  not (get sDiffSystem se) && (
      (isMsgVar m && isNothing (M.lookup i (get sNodes se)))
    || sortOfLNTerm m == LSortPub
    || sortOfLNTerm m == LSortNat
    || isPair m
    || isInverse m
    || isProduct m
    || isUnion m
    || isNullaryPublicFunction m)
isRedundant se (ChainG c p) = case kFactView (nodeConcFact c se) of
  -- do not solve Union conclusions if they contain only known msg vars
  Just (DnK, viewTerm2 -> FUnion args) -> allMsgVarsKnownEarlier c args
  -- open chains for msg vars are only solved if N5'' is applicable
  Just (DnK,  m)  | isMsgVar m -> not (chainToEquality m)
                  | otherwise  -> False
  _ -> False
  where
    allMsgVarsKnownEarlier (i, _) args = all isMsgVar args
      && all (`elem` earlierMsgVars) args
      where
        earlierMsgVars = do
          (j, _, t) <- allKUActions se
          guard (isMsgVar t && alwaysBefore se j i)
          return t

    -- check whether we have a chain that fits N5'' (an open chain between an
    -- equality rule and a simple msg var conclusion that exists as a K up
    -- previously) which needs to be resolved even if it is an open chain
    chainToEquality :: LNTerm -> Bool
    chainToEquality t_start = isMsgVar t_start && is_equality && ku_before
      where
        -- and whether we do have an equality rule instance at the end
        is_equality = isIEqualityRule $ nodeRule (fst p) se
        -- get all KU-facts with the same msg var
        ku_start    = filter (\x -> fst x == t_start) $
                        map (\(i, _, m) -> (m, i)) $ allKUActions se
        -- and check whether any of them happens before the KD-conclusion
        ku_before   = any (\(_, x) -> alwaysBefore se x (fst c)) ku_start
isRedundant _ _ = False

mustBeSolved :: System -> [(Goal, GoalStatus)]
mustBeSolved se = filter (uncurry p) $ M.toList $ get sGoals se
  where
    p :: Goal -> GoalStatus -> Bool
    p g gs = goalP g && not (get gsSolved gs)

    goalP :: Goal -> Bool
    goalP (Cut _) = False
    goalP (Weaken _) = False
    goalP SearchBacklink = False
    goalP g = not $ isRedundant se g

isSolved :: System -> Bool
isSolved sys = not (isInitialSystem sys) && null (mustBeSolved sys)

-- | The list of goals that can be solved. Each goal is annotated with its age
--   and an indicator for its usefulness.
annotateGoals :: System -> [AnnotatedGoal]
annotateGoals sys = do
    (goal, status) <- filter (uncurry mayBeSolved) (M.toList (get sGoals sys))
    let useful = case goal of
          (Cut _) -> Useful
          _ | get gsLoopBreaker status -> LoopBreaker
          ActionG i (kFactView -> Just (UpK, m))
              -- if there are KU-guards then all knowledge goals are useful
            | hasKUGuards             -> Useful
            | currentlyDeducible i m  -> CurrentlyDeducible
            | probablyConstructible m -> ProbablyConstructible
          _                           -> Useful

    return (goal, (get gsNr status, useful))
  where
    mayBeSolved :: Goal -> GoalStatus -> Bool
    mayBeSolved g gs = not (isRedundant sys g) && not (get gsSolved gs)

    existingDeps = rawLessRel sys
    hasKUGuards  =
        any ((KUFact `elem`) . guardFactTags) $ S.toList $ get sFormulas sys

    checkTermLits :: (LSort -> Bool) -> LNTerm -> Bool
    checkTermLits p =
        Mono.getAll . foldMap (Mono.All . p . sortOfLit)

    -- KU goals of messages that are likely to be constructible by the
    -- adversary. These are terms that do not contain a fresh name or a fresh
    -- name variable. For protocols without loops they are very likely to be
    -- constructible. For protocols with loops, such terms have to be given
    -- similar priority as loop-breakers.
    probablyConstructible  m = checkTermLits (LSortFresh /=) m
                               && not (containsPrivate m)

    -- KU goals of messages that are currently deducible. Either because they
    -- are composed of public names only and do not contain private function
    -- symbols or because they can be extracted from a sent message using
    -- unpairing or inversion only.
    currentlyDeducible i m = (checkTermLits (`elem` [LSortPub, LSortNat]) m
                              && not (containsPrivate m))
                          || extractible i m

    extractible i m = or $ do
        (j, ru) <- M.toList $ get sNodes sys
        -- We cannot deduce a message from a last node.
        guard (not $ isLast sys j)
        let derivedMsgs = concatMap toplevelTerms $
                [ t | Fact OutFact _ _ [t] <- get rConcs ru] <|>
                [ t | Just (DnK, t)        <- kFactView <$> get rConcs ru]
        -- m is deducible from j without an immediate contradiction
        -- if it is a derived message of 'ru' and the dependency does
        -- not make the graph cyclic.
        return $ m `elem` derivedMsgs &&
                 not (j `S.member` D.reachableSet [i] existingDeps)

    toplevelTerms t@(viewTerm2 -> FPair t1 t2) =
        t : toplevelTerms t1 ++ toplevelTerms t2
    toplevelTerms t@(viewTerm2 -> FInv t1) = t : toplevelTerms t1
    toplevelTerms t = [t]

-- | The list of all open goals left together with their status.
plainOpenGoals:: System -> [(Goal, GoalStatus)]
plainOpenGoals = filter (not . get gsSolved . snd) . M.toList . L.get sGoals

------------------------------------------------------------------------------
-- Solving 'Goal's
------------------------------------------------------------------------------

-- | @solveGoal rules goal@ enumerates all possible cases of how this goal
-- could be solved in the context of the given @rules@. For each case, a
-- sensible case-name is returned.
solveGoal :: Maybe (NE.NonEmpty System) -> Goal -> Reduction String
solveGoal syss goal = do
    -- mark before solving, as representation might change due to unification
    markGoalAsSolved "directly" goal
    rules <- askM pcRules
    case goal of
      ActionG i fa  -> solveAction (nonSilentRules rules) (i, fa)
      PremiseG p fa ->
           solvePremise (get crProtocol rules ++ get crConstruct rules) p fa
      ChainG c p    -> solveChain (get crDestruct  rules) (c, p)
      SplitG i      -> solveSplit i
      DisjG disj    -> solveDisjunction disj
      SubtermG st   -> solveSubterm st
      Weaken el     -> weaken el >> return ""
      Cut el        -> cut syss el
      SearchBacklink -> searchBacklink True syss >> return ""

-- The following functions are internal to 'solveGoal'. Use them with great
-- care.

-- | CR-rule *S_at*: solve an action goal.
solveAction :: [RuleAC]          -- ^ All rules labelled with an action
            -> (NodeId, LNFact)  -- ^ The action we are looking for.
            -> Reduction String  -- ^ A sensible case name.
solveAction rules (i, fa@(Fact _ ann _ _)) = do
    mayRu <- M.lookup i <$> getM sNodes
    showRuleCaseName <$> case mayRu of
        Nothing -> case fa of
            (Fact KUFact _ _ [m@(viewTerm2 -> FXor ts)]) -> do
                   partitions <- disjunctionOfList $ twoPartitions ts
                   case partitions of
                       (_, []) -> do
                            let ru = Rule (IntrInfo CoerceRule) [kdFact m] [fa] [fa] []
                            modM sNodes (M.insert i ru)
                            insertGoal (PremiseG (i, PremIdx 0) (kdFact m)) False
                            return ru
                       (a',  b') -> do
                            let a = fAppAC Xor a'
                            let b = fAppAC Xor b'
                            let ru = Rule (IntrInfo (ConstrRule $ BC.pack "_xor")) [(kuFact a),(kuFact b)] [fa] [fa] []
                            modM sNodes (M.insert i ru)
                            mapM_ requiresKU [a, b] *> return ru
            _                                        -> do
                   ru  <- labelNodeId i (annotatePrems <$> rules) Nothing
                   act <- disjunctionOfList $ get rActs ru
                   void (solveFactEqs SplitNow [Equal fa act])
                   return ru

        Just ru -> do unless (fa `elem` get rActs ru) $ do
                          act <- disjunctionOfList $ get rActs ru
                          void (solveFactEqs SplitNow [Equal fa act])
                      return ru
  where
    -- If the fact in the action goal has annotations, then consider annotated
    -- versions of intruder rules (this allows high or low priority intruder knowledge
    -- goals to propagate to intruder knowledge of subterms)
    annotatePrems ru@(Rule ri ps cs as nvs) =
        if not (S.null ann) && isIntruderRule ru then
            Rule ri (annotateFact ann <$> ps) cs (annotateFact ann <$> as) nvs
            else ru
    requiresKU t = do
        j <- freshLVar "vk" LSortNode
        let faKU = kuFact t
        insertLess (LessAtom j i Adversary)
        void (insertAction j faKU)

-- | CR-rules *DG_{2,P}* and *DG_{2,d}*: solve a premise with a direct edge
-- from a unifying conclusion or using a destruction chain.
--
-- Note that *In*, *Fr*, and *KU* facts are solved directly when adding a
-- 'ruleNode'.
--
solvePremise :: [RuleAC]       -- ^ All rules with a non-K-fact conclusion.
             -> NodePrem       -- ^ Premise to solve.
             -> LNFact         -- ^ Fact required at this premise.
             -> Reduction String -- ^ Case name to use.
solvePremise rules p faPrem
  | isKDFact faPrem = do
      iLearn    <- freshLVar "vl" LSortNode
      mLearn    <- varTerm <$> freshLVar "t" LSortMsg
      let concLearn = kdFact mLearn
          premLearn = outFact mLearn
          -- !! Make sure that you construct the correct rule!
          ruLearn = Rule (IntrInfo IRecvRule) [premLearn] [concLearn] [] []
          cLearn = iLearn
          pLearn = (iLearn, PremIdx 0)
      modM sNodes  (M.insert iLearn ruLearn)
      insertChain cLearn p
      solvePremise rules pLearn premLearn

  | otherwise = do
      (ru, c, faConc) <- insertFreshNodeConc rules
      insertEdges [(c, faConc, faPrem, p)]
      return $ showRuleCaseName ru

-- | CR-rule *DG2_chain*: solve a chain constraint.
solveChain :: [RuleAC]              -- ^ All destruction rules.
           -> (NodeConc, NodePrem)  -- ^ The chain to extend by one step.
           -> Reduction String      -- ^ Case name to use.
solveChain rules (c, p) = do
    faConc  <- gets $ nodeConcFact c
    do -- solve it by a direct edge
        cRule <- gets $ nodeRule (nodeConcNode c)
        pRule <- gets $ nodeRule (nodePremNode p)
        faPrem <- gets $ nodePremFact p
        contradictoryIf (forbiddenEdge cRule pRule)
        insertEdges [(c, faConc, faPrem, p)]
        let mPrem = case kFactView faConc of
                      Just (DnK, m') -> m'
                      _              -> error "solveChain: impossible"
            caseName (viewTerm -> FApp o _)    = showFunSymName o
            caseName (viewTerm -> Lit l)       = showLitName l
        contradictoryIf (illegalCoerce pRule mPrem)
        return (caseName mPrem)
     `disjunction`
     -- extend it with one step
     case kFactView faConc of
         Just (DnK, viewTerm2 -> FUnion args) ->
             do -- If the chain starts at a union message, we
                -- compute the applicable destruction rules directly.
                i <- freshLVar "vr" LSortNode
                let rus = map (ruleACIntrToRuleACInst . mkDUnionRule args)
                              args
                -- NOTE: We rely on the check that the chain is open here.
                ru <- disjunctionOfList rus
                modM sNodes (M.insert i ru)
                -- FIXME: Do we have to add the PremiseG here so it
                -- marked as solved?
                let v = PremIdx 0
                faPrem <- gets $ nodePremFact (i,v)
                extendAndMark i ru v faPrem faConc
         Just (DnK, m) ->
             do -- If the chain does not start at a union message,
                -- the usual *DG2_chain* extension is perfomed.
                -- But we ignore open chains, as we only resolve
                -- open chains with a direct chain
                contradictoryIf (isMsgVar m)
                cRule <- gets $ nodeRule (nodeConcNode c)
                (i, ru) <- insertFreshNode rules (Just cRule)
                contradictoryIf (forbiddenEdge cRule ru)
                -- This requires a modified chain constraint def:
                -- path via first destruction premise of rule ...
                (v, faPrem) <- disjunctionOfList $ take 1 $ enumPrems ru
                extendAndMark i ru v faPrem faConc
         _ -> error "solveChain: not a down fact"
  where
    extendAndMark :: NodeId -> RuleACInst -> PremIdx -> LNFact -> LNFact
      -> Reduction String
    extendAndMark i ru v faPrem faConc = do
        insertEdges [(c, faConc, faPrem, (i, v))]
        markGoalAsSolved "directly" (PremiseG (i, v) faPrem)
        insertChain i p
        return (showRuleCaseName ru)

    -- contradicts normal form condition:
    -- no edge from dexp to dexp KD premise, no edge from dpmult
    -- to dpmult KD premise, and no edge from dpmult to demap KD premise
    -- (this condition replaces the exp/noexp tags)
    -- no more than the allowed consecutive rule applications
    forbiddenEdge :: RuleACInst -> RuleACInst -> Bool
    forbiddenEdge cRule pRule = isDExpRule   cRule && isDExpRule  pRule  ||
                                isDPMultRule cRule && isDPMultRule pRule ||
                                isDPMultRule cRule && isDEMapRule  pRule ||
                                (getRuleName cRule == getRuleName pRule)
                                    && (getRemainingRuleApplications cRule == 1)

    -- Contradicts normal form condition N2:
    -- No coerce of a pair of inverse.
    illegalCoerce pRule mPrem = isCoerceRule pRule && isPair    mPrem ||
                                isCoerceRule pRule && isInverse mPrem ||
    -- Also: Coercing of products is unnecessary, since the protocol is *-restricted.
                                isCoerceRule pRule && isProduct mPrem


-- | Solve an equation split. There is no corresponding CR-rule in the rule
-- system on paper because there we eagerly split over all variants of a rule.
-- In practice, this is too expensive and we therefore use the equation store
-- to delay these splits.
solveSplit :: SplitId -> Reduction String
solveSplit x = do
    split <- gets ((`performSplit` x) . get sEqStore)
    let errMsg = error "solveSplit: inexistent split-id"
    store      <- maybe errMsg disjunctionOfList split
    -- FIXME: Simplify this interaction with the equation store
    hnd        <- getMaudeHandle
    substCheck <- gets (substCreatesNonNormalTerms hnd)
    store'     <- simp hnd substCheck store
    contradictoryIf (eqsIsFalse store')
    sEqStore =: store'
    return "split"

-- | CR-rule *S_disj*: solve a disjunction of guarded formulas using a case
-- distinction.
--
-- In contrast to the paper, we use n-ary disjunctions and also split over all
-- of them at once.
solveDisjunction :: Disj LNGuarded -> Reduction String
solveDisjunction disj = do
    (i, gfm) <- disjunctionOfList $ zip [(1::Int)..] $ getDisj disj
    insertFormula gfm
    return $ "case_" ++ show i

-- | remove from subterms
-- get split
-- behave according to split
--   insert subterms
--   insert equalities
--   insert eqFormulas
--   ignore TrueD
--   contradict if emptyset
solveSubterm :: (LNTerm, LNTerm) -> Reduction String
solveSubterm st = do
      -- mark subterm as solved
      modM (posSubterms . sSubtermStore) (st `S.delete`)
      modM (solvedSubterms . sSubtermStore) (st `S.insert`)
      
      -- find all splits
      reducible <- reducibleFunSyms . mhMaudeSig <$> getMaudeHandle
      splitList <- splitSubterm reducible True st
      (i, split) <- disjunctionOfList $ zip [(1::Int)..] splitList  -- make disjunction over all splits
      
      -- from here on: only look at a single split
      case split of
        TrueD -> return ()
        SubtermD st1 -> modM sSubtermStore (addSubterm st1)
        NatSubtermD st1@(s,t) -> if length splitList == 1
                                    then do
                                      newVar <- freshLVar "newVar" LSortNat
                                      let sPlus = s ++: varTerm newVar
                                      insertFormula $ closeGuarded Ex [newVar] [EqE sPlus t] gtrue
                                    else modM sSubtermStore (addSubterm st1)
        EqualD (l, r) -> insertFormula $ GAto $ EqE (lTermToBTerm l) (lTermToBTerm r)
        ACNewVarD ((smallPlus, big), newVar) -> insertFormula $ closeGuarded Ex [newVar] [EqE smallPlus big] gtrue
        
      return $ "SubtermSplit" ++ show i

fromTail :: LoopInstance NodeId -> NE.NonEmpty NodeId -> LoopInstance NodeId
fromTail li es@(h :| _) = li { start = h, loopEdges = es }

fromPrefix :: LoopInstance NodeId -> NE.NonEmpty NodeId -> LoopInstance NodeId
fromPrefix li es = li { end = NE.last es, loopEdges = es }

splitLoopsAtNode :: NodeId -> [LoopInstance NodeId] -> [LoopInstance NodeId]
splitLoopsAtNode _ [] = []
splitLoopsAtNode n (li@LoopInstance { loopEdges = es }:t)
  | null r = li : splitLoopsAtNode n t
  | otherwise = catMaybes [liL, liR] ++ t
  where
    (l, r) = NE.break (== n) es
    liL = fromPrefix li <$> NE.nonEmpty l
    liR = do
      esL' <- peakTail r
      es' <- NE.nonEmpty esL'
      return $ fromTail li es'

splitLoopsAtEdge :: Edge -> [LoopInstance NodeId] -> [LoopInstance NodeId]
splitLoopsAtEdge _ [] = []
splitLoopsAtEdge e@(Edge (src, _) (tgt, _)) (li@(LoopInstance { loopEdges = es }):t)
  | not (null r) = fromPrefix li l : fromTail li (NE.fromList r) : t
  | otherwise = li : splitLoopsAtEdge e t
  where
    (l, r) = splitBetween (src, tgt) es

data WeakenMode = Preserve | Prune deriving Eq

weaken :: WeakenEl -> Reduction ()
weaken el = do
  sid <- L.getM sId
  L.setM sWeakenedFrom (Just sid)
  go el
  where
    activateGoals :: (Goal -> Bool) -> Reduction ()
    activateGoals p = L.modM sGoals modGoals
      where
        modGoals :: M.Map Goal GoalStatus -> M.Map Goal GoalStatus
        modGoals goals = foldr (M.update (Just . set gsSolved False)) goals (filter p (M.keys goals))

    weakenEdge :: WeakenMode -> Edge -> Reduction ()
    weakenEdge mode e@(Edge conc prem) = do
      L.modM sEdges (S.delete e)
      L.modM sLoops (splitLoopsAtEdge e)
      when (mode == Preserve) $ do
        L.modM sLessAtoms (S.insert (lessAtomFromEdge KeepWeakened e))
        activateGoals premiseAndChainGoals
      where
        premiseAndChainGoals :: Goal -> Bool
        premiseAndChainGoals (PremiseG prem' _) = prem' == prem
        premiseAndChainGoals (ChainG conc' prem') = conc' == conc && prem' == prem
        premiseAndChainGoals _ = False

    weakenNode :: WeakenMode -> NodeId -> Reduction ()
    weakenNode mode i = do
        L.modM sNodes $ M.delete i
        L.modM sGoals $ M.filterWithKey keepGoal
        L.modM sLoops (splitLoopsAtNode i)
        (toKeep, toDeleteOutgoing) <- S.partition ((/= i) . fst . eSrc) <$> L.getM sEdges
        let (_, toDeleteIncoming) = S.partition ((/= i) . fst . eTgt) toKeep
        mapM_ (weakenEdge mode) toDeleteOutgoing
        -- KU goals are similar to premise goals and thus we re-active them
        mapM_ (weakenEdge mode) toDeleteIncoming
        when (mode == Preserve) (activateGoals kuGoals)
        when (mode == Prune) (L.modM sLessAtoms (S.filter keepLessAtom))
      where
        keepGoal :: Goal -> a -> Bool
        keepGoal (PremiseG (i', _) _) _ = i /= i'
        keepGoal (ChainG _ (i', _)) _ = i' /= i
        keepGoal (ActionG i' _) _ = mode == Preserve || i' /= i
        keepGoal _ _ = True

        kuGoals :: Goal -> Bool
        kuGoals (ActionG i' f) = i' == i && isKUFact f
        kuGoals _ = False

        keepLessAtom :: LessAtom -> Bool
        keepLessAtom (LessAtom nid1 nid2 _) = nid1 /= i && nid2 /= i

    go :: WeakenEl -> Reduction ()
    go WeakenCyclic = do
      loops <- L.getM sLoops
      mFwd <- forwardReachability
      mBackwd <- backwardReachability
      when (not (null loops) && isJust mFwd && isJust mBackwd) $ do
        let fwd = fromJust mFwd
        let backwd = fromJust mBackwd
        let loopNodes = foldr (flip (foldr S.insert)) S.empty loops

        mapM_ (mapM_ (weakenNode Prune) . getLarger fwd . end) loops
        mapM_ (keepLoopShort loopNodes fwd backwd) loops
        nodes <- M.toList <$> L.getM sNodes
        -- Delete all K nodes
        nonLeafs <- gets (S.fromList . map fst . rawLessRel)
        let isLeaf = not . (`S.member` nonLeafs)
        let kLeafs = filters all [isISendRule . snd, isLeaf . fst] nodes
        mapM_ (weakenNode Prune . fst) kLeafs
        let isLeafNow n = isLeaf n || any (S.member n . getDirectlyLarger backwd . fst) kLeafs
        mapM_ (keepKuChainShort backwd . fst) $ filters all [isConstrRule . snd, isLeafNow . fst] nodes
      where
        filters acc ps = filter (\a -> acc ($ a) ps)

        reachability :: (System -> [(NodeId, NodeId)]) -> Reduction (Maybe (TransClosedOrder NodeId))
        reachability f = do
          rel <- gets f
          return (fromSet (S.fromList rel))

        forwardReachability :: Reduction (Maybe (TransClosedOrder NodeId))
        forwardReachability = reachability (\s -> kLessRel s ++ rawEdgeRel s)

        backwardReachability :: Reduction (Maybe (TransClosedOrder NodeId))
        backwardReachability = reachability (map swap . (\s -> kLessRel s ++ rawEdgeRel s))

        keepLoopShort :: S.Set NodeId -> TransClosedOrder NodeId -> TransClosedOrder NodeId -> LoopInstance NodeId -> Reduction ()
        keepLoopShort loopNodes fwd backwd ls = do
          let t = NE.tail (loopEdges ls)
          mapM_ (weakenNode Preserve) t
          mapM_ (\n -> mapM_ (prunePremiseSources n) $ getDirectlyLarger backwd n) t
            where
              prunePremiseSources :: NodeId -> NodeId -> Reduction ()
              prunePremiseSources parent i = do
                let noOutgoing = S.singleton parent == getDirectlyLarger fwd i
                when (noOutgoing && (i `S.notMember` loopNodes)) $ do
                  weakenNode Prune i
                  mapM_ (prunePremiseSources i) $ getDirectlyLarger backwd i

        keepKuChainShort :: TransClosedOrder NodeId -> NodeId -> Reduction ()
        keepKuChainShort backwd i = do
          nodes <- L.getM sNodes
          let isGoalOnly = not (M.member i nodes)
          -- Only weaken if a KU node is reachable from this one or if this is a
          -- pure action goal
          when (isGoalOnly || any (maybe False isConstrRule . (`M.lookup` nodes)) (getLarger backwd i)) $ do
            weakenNode Prune i
            mapM_ (keepKuChainShort backwd) (getDirectlyLarger backwd i)
    go (WeakenFormula f) = L.modM sFormulas (S.delete f)
    go (WeakenLessAtom nid1 nid2) = L.modM sLessAtoms (S.filter keepLatom)
      where
        keepLatom :: LessAtom -> Bool
        keepLatom (LessAtom sml lrg _) = sml /= nid1 || lrg /= nid2
    go (WeakenGoal g) = L.modM sGoals (M.delete g)
    go (WeakenEdge e) = weakenEdge Preserve e
    go (WeakenNode i) = weakenNode Preserve i

cut :: Maybe (NE.NonEmpty System) -> UpTo -> Reduction String
cut syss (S.toList -> phis) = join $ disjunctionOfList (cutCase : zipWith negCase [(0 :: Int)..] phis)
  where
    insertFormulas :: [LNGuarded] -> Reduction ()
    insertFormulas formulas = L.modM sFormulas (\s -> foldr S.insert s formulas)

    cutCase :: Reduction String
    cutCase = do
      insertFormulas phis
      searchBacklink False syss
      return "cut"

    negCase :: Int -> LNGuarded -> Reduction String
    negCase i phi = do
      insertFormulas [gnot phi]
      return $ "negate_" ++ show i

searchBacklink :: Bool -> Maybe (NE.NonEmpty System) -> Reduction ()
searchBacklink asMethod syssToRoot = do
  ctxt <- ask
  s <- St.get
  let syss = bool (s NE.<|) id asMethod <$> syssToRoot
  maybe (return ()) cycleFound (syss >>= getCycleRenamingOnPath ctxt)
  where
    cycleFound :: BackLinkCandidate -> Reduction ()
    cycleFound (PartialCyclicProof upTo bl) = if S.null upTo
      then tell (Just (Contradictory (Just (Cyclic bl))))
      else when asMethod (insertGoal (Cut upTo) False)

insertMinimize :: Reduction ()
insertMinimize = do
  present <- M.member (Weaken WeakenCyclic) <$> getM sGoals
  unless present (insertGoal (Weaken WeakenCyclic) True)

insertSearchBacklink :: Reduction ()
insertSearchBacklink = do
  present <- M.member SearchBacklink <$> getM sGoals
  cutPresent <- any isCut . M.keys <$> getM sGoals
  when (not present && not cutPresent) (insertGoal SearchBacklink True)
  where
    isCut :: Goal -> Bool
    isCut (Cut _) = True
    isCut _ = False

insertCyclicGoals :: Reduction ()
insertCyclicGoals = do
  ctxt <- ask
  when (doCyclicInduction ctxt) $ do
    -- It is important to insert backlink search before minimzation so that
    -- backlinks are searched before minimization is done.
    insertSearchBacklink
    insertMinimize
