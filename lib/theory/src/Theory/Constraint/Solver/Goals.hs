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
  , reduceFormulas
  , enforceEdgeUniqueness
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
import           Theory.Constraint.System.ID (SystemID)
import           Theory.Tools.IntruderRules (mkDUnionRule, isDExpRule, isDPMultRule, isDEMapRule)
import           Theory.Model
import           Term.Builtin.Convenience


import Utils.Misc (twoPartitions, peakTail, splitBetween)
import Data.Maybe (isNothing, catMaybes, mapMaybe, fromMaybe)
import Theory.Constraint.System.Inclusion (InclusionFailure, BackLinkCandidate (blUpTo, bl), prefixMatchesOnPath)
import Data.List.NonEmpty as NE (NonEmpty((:|)))
import Utils.PartialOrd (TransClosedOrder(..), fromSet, getLarger, getDirectlyLarger, minima)
import Control.Monad.RWS (MonadReader(ask), MonadWriter (tell))
import Theory.Constraint.System.Results (Result(Contradictory), Contradiction (Cyclic))
import Data.Bool (bool)
import Data.List (find, group, sort)
import Debug.Trace (traceM)
import Extension.Prelude (groupSortOn)

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
      Weaken el     -> weaken el
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

-- | Reduce all formulas as far as possible. See 'insertFormula' for the
-- CR-rules exploited in this step. Note that this step is normally only
-- required to decompose the formula in the initial constraint system.
reduceFormulas :: Reduction ChangeIndicator
reduceFormulas = do
    formulas <- getM sFormulas
    applyChangeList $ do
        fm <- S.toList formulas
        guard (reducibleFormula fm)
        return $ do modM sFormulas $ S.delete fm
                    insertFormula fm

-- | CR-rules *DG2_1* and *DG3*: merge multiple incoming edges to all facts
-- and multiple outgoing edges from linear facts.
enforceEdgeUniqueness :: Reduction ChangeIndicator
enforceEdgeUniqueness = do
    se <- gets id
    let edges = S.toList (get sEdges se)
    (<>) <$> mergeNodes eSrc eTgt edges
         <*> mergeNodes eTgt eSrc (filter (proveLinearConc se . eSrc) edges)
  where
    -- | @proveLinearConc se (v,i)@ tries to prove that the @i@-th
    -- conclusion of node @v@ is a linear fact.
    proveLinearConc se (v, i) =
        maybe False (isLinearFact . (get (rConc i))) $
            M.lookup v $ get sNodes se

    -- merge the nodes on the 'mergeEnd' for edges that are equal on the
    -- 'compareEnd'
    mergeNodes mergeEnd compareEnd edges
      | null eqs  = return Unchanged
      | otherwise = do
            -- all indices of merged premises and conclusions must be equal
            contradictoryIf (not $ and [snd l == snd r | Equal l r <- eqs])
            -- nodes must be equal
            solveNodeIdEqs $ map (fmap fst) eqs
      where
        eqs = concatMap (merge mergeEnd) $ groupSortOn compareEnd edges

        merge _    []            = error "exploitEdgeProps: impossible"
        merge proj (keep:remove) = map (Equal (proj keep) . proj) remove

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

-- NOTE: It is critical for soundness that weakening introduces no new
-- constraints (unless they are cut). In particular, no constraints marked as
-- solved (formulas or goals or ...) must be marked as unsolved. Cyclic proofs
-- consider solved goals as implicitly weakened, i.e., they should only be
-- reintroduced if a constraint solving rule would allow for this.
weaken :: WeakenEl -> Reduction String
weaken el = do
  sid <- L.getM sId
  L.setM sWeakenedFrom (Just sid)
  go el
  where
    weakenEdge :: WeakenMode -> Edge -> Reduction String
    weakenEdge mode e = do
      L.modM sEdges (S.delete e)
      L.modM sLoops (splitLoopsAtEdge e)
      when (mode == Preserve) $ do
        L.modM sLessAtoms (S.insert (lessAtomFromEdge KeepWeakened e))
      return ""

    weakenNode :: WeakenMode -> NodeId -> Reduction String
    weakenNode mode i = do
        L.modM sNodes $ M.delete i
        L.modM sGoals $ M.filterWithKey keepGoal
        L.modM sLoops (splitLoopsAtNode i)
        (toKeep, toDeleteOutgoing) <- S.partition ((/= i) . fst . eSrc) <$> L.getM sEdges
        let (_, toDeleteIncoming) = S.partition ((/= i) . fst . eTgt) toKeep
        mapM_ (weakenEdge mode) toDeleteOutgoing
        mapM_ (weakenEdge mode) toDeleteIncoming
        when (mode == Prune) (L.modM sLessAtoms (S.filter keepLessAtom))
        return ""
      where
        keepGoal :: Goal -> GoalStatus -> Bool
        keepGoal (PremiseG (i', _) _) _ = i /= i'
        keepGoal (ChainG _ (i', _)) _ = i' /= i
        keepGoal (ActionG i' _) _ = i' /= i
        keepGoal _ _ = True

        keepLessAtom :: LessAtom -> Bool
        keepLessAtom (LessAtom nid1 nid2 _) = nid1 /= i && nid2 /= i

    go :: WeakenEl -> Reduction String
    go WeakenCyclic = do
      loops <- L.getM sLoops
      -- Nothing deactivates backlink search; if loopCuts is empty, single case
      -- will be returned
      let (toWeaken NE.:| cutNegation) = cutCases Nothing (loopCuts loops)
      -- forward reachability
      mFwd <- gets (\s -> fromSet $ S.fromList $ kLessRel s ++ rawEdgeRel s)
      join $ disjunctionOfList $ (toWeaken >> doWeakening loops mFwd) : map (<* unifyEdges) cutNegation
      where
        doWeakening :: [LoopInstance NodeId] -> Maybe (TransClosedOrder NodeId) -> Reduction String
        doWeakening _ Nothing = return "weaken"
        doWeakening loops (Just fwd) = do
          nodes <- L.getM sNodes
          let starts = S.fromList $ map start loops
          let loopTails = foldr (S.union . getLarger fwd . start) S.empty loops
          let kuToWeakenFrom = kuWeakenSources nodes
          let kLeafs = S.fromList
                $ filter (S.null . getDirectlyLarger fwd)
                $ map fst
                $ filter (isISendRule . snd)
                $ M.toList nodes
          let kuToWeaken = foldr (S.union . getLarger fwd) S.empty kuToWeakenFrom
          let (nodesToWeaken, _) = foldr addPremisesToWeaken (loopTails <> kuToWeaken, (starts S.\\ loopTails) <> kuToWeakenFrom) (minima fwd)
          mapM_ (\n -> weakenNode (if n `S.member` loopTails then Preserve else Prune) n) nodesToWeaken
          mapM_ (weakenNode Prune) kLeafs
          edges <- getM sEdges
          mapM_ (weakenEdge Preserve) $ S.filter (isLoopToLoopEdge nodes) edges

          return "weaken"
          where
            isLoopToLoopEdge :: M.Map NodeId RuleACInst -> Edge -> Bool
            isLoopToLoopEdge ns (Edge (concN, concIdx) (premN, _)) =
              let isLoopFactConsumed = fromMaybe False $ do
                    li <- find ((== concN) . start) loops
                    r <- M.lookup concN ns
                    return $ loopFact li == factTag (L.get (rConc concIdx) r)
              in isLoopFactConsumed && premN `elem` map start loops

            kuWeakenSources :: M.Map NodeId RuleACInst -> S.Set NodeId
            kuWeakenSources ns =
              let kuNodes = M.keysSet $ M.filter isConstrRule ns
                  -- ^ All KU nodes
                  disconnectedKUNodes = S.filter (all intruder . getLarger fwd) kuNodes
                  -- ^ All KU nodes that have only action goals, KU nodes, or K nodes larger then them
              in  foldr (\n -> (S.\\ getLarger fwd n)) disconnectedKUNodes disconnectedKUNodes
                  -- ^ Remove all larger nodes from the set so that there are only the topmost KU nodes left
              where
                intruder :: NodeId -> Bool
                intruder n = maybe True isIntruderRule (M.lookup n ns)

            addPremisesToWeaken :: NodeId -> (S.Set NodeId, S.Set NodeId) -> (S.Set NodeId, S.Set NodeId)
            addPremisesToWeaken n (delete, keep)
              | n `S.member` keep = (delete, keep)
              | n `S.member` delete = (delete, keep)
              | otherwise =
                let larger = getDirectlyLarger fwd n
                    (delete', keep') = foldr addPremisesToWeaken (delete, keep) larger
                in  if S.null larger then (delete, keep)
                    else if all (`S.member` delete') larger then (S.insert n delete', keep')
                    else (delete', S.insert n keep')

        unifyEdges :: Reduction ()
        unifyEdges = do
          _ <- substSystem
          void enforceEdgeUniqueness

        loopCuts :: [LoopInstance NodeId] -> S.Set LNGuarded
        loopCuts [] = S.empty
        loopCuts (l:ls) = rec l ls <> loopCuts ls
          where
            toBTerm :: NodeId -> BLTerm
            toBTerm = lTermToBTerm . varTerm

            unifGuard :: LoopInstance NodeId -> LoopInstance NodeId -> Maybe LNGuarded
            unifGuard (LoopInstance { loopFact = f, loopEdges = es }) (LoopInstance { loopFact = f', loopEdges = es' }) = do
              guard (f == f')
              let loopNodesEqual = NE.zipWith (\t1 t2 -> GAto (EqE (toBTerm t1) (toBTerm t2))) es es'
              guard (not $ null $ NE.tail loopNodesEqual)
              return (gdisj [ gnot (NE.head loopNodesEqual), NE.last loopNodesEqual ])

            rec :: LoopInstance NodeId -> [LoopInstance NodeId] -> S.Set LNGuarded
            rec _ [] = S.empty
            rec li (li':t) = maybe id S.insert (unifGuard li li') (rec li t)
    go (WeakenFormula phi) = do
      L.modM sFormulas (S.delete phi)
      L.modM sGoals (M.filterWithKey (\k _ -> not $ associatedSplitGoal k))
      return ""
      where
        associatedSplitGoal :: Goal -> Bool
        associatedSplitGoal (DisjG disj) = phi == GDisj disj
        associatedSplitGoal _ = False
    go (WeakenLessAtom nid1 nid2) = do
      L.modM sLessAtoms (S.filter keepLatom)
      return ""
      where
        keepLatom :: LessAtom -> Bool
        keepLatom (LessAtom sml lrg _) = sml /= nid1 || lrg /= nid2
    go (WeakenGoal g) = do
      L.modM sGoals (M.delete g)
      return ""
    go (WeakenEdge e) = weakenEdge Preserve e
    go (WeakenNode i) = weakenNode Preserve i

cut :: Maybe (NE.NonEmpty System) -> UpTo -> Reduction String
cut syss = join . disjunctionOfList . NE.toList . cutCases syss

cutCases :: Maybe (NE.NonEmpty System) -> UpTo -> NE.NonEmpty (Reduction String)
cutCases syss (S.toList -> phis) = cutCase NE.:| zipWith negCase [(0 :: Int)..] phis
  where
    insertFormulas :: [LNGuarded] -> Reduction ()
    insertFormulas formulas = L.modM sFormulas (\s -> foldr S.insert s formulas)

    cutCase :: Reduction String
    cutCase = do
      insertFormulas phis
      _ <- reduceFormulas
      searchBacklink False syss
      return "cut"

    negCase :: Int -> LNGuarded -> Reduction String
    negCase i phi = do
      insertFormulas [gnot phi]
      _ <- reduceFormulas
      return $ "negate_" ++ show i

searchBacklink :: Bool -> Maybe (NE.NonEmpty System) -> Reduction ()
searchBacklink asMethod syssToRoot = do
  ctxt <- ask
  s <- St.get
  let syss = bool (s NE.<|) id asMethod <$> syssToRoot
  maybe (return ()) (either traceFailure cycleFound . prefixMatchesOnPath ctxt) syss
  where
    insertCut :: [BackLinkCandidate] -> Reduction ()
    insertCut = when asMethod . mapM_ (\(blUpTo -> ut) -> insertGoal (Cut ut) False)

    setContradictory :: BackLinkCandidate -> Reduction ()
    setContradictory = tell . Just . Contradictory . Just . Cyclic . bl

    showNEFails :: NE.NonEmpty InclusionFailure -> String
    showNEFails (h NE.:| []) = show h
    showNEFails l@(h NE.:| _) = show h ++ " (" ++ show (NE.length l) ++ " times)"

    traceFailureSystem :: (SystemID, [InclusionFailure]) -> Reduction ()
    traceFailureSystem (sid, fails) = do
      traceM $ " * For system " ++ show sid
      if null fails
        then traceM "   * No match found"
        else mapM_ (traceM . ("   * " ++) . showNEFails) $ mapMaybe NE.nonEmpty $ group $ sort fails

    traceFailure :: [(SystemID, [InclusionFailure])] -> Reduction ()
    traceFailure fails = do
      traceM "NO CYCLE -- Reason(s): "
      mapM_ traceFailureSystem fails

    cycleFound :: [BackLinkCandidate] -> Reduction ()
    cycleFound cands = maybe (insertCut cands) setContradictory (find (S.null . blUpTo) cands)
      -- maybe (mapM_ insertCut cands) setContradictory (find (S.null . blUpTo) =<< cands)

insertMinimize :: Reduction ()
insertMinimize = do
  present <- M.member (Weaken WeakenCyclic) <$> getM sGoals
  unless present (insertGoal (Weaken WeakenCyclic) True)

insertSearchBacklink :: Reduction ()
insertSearchBacklink = do
  present <- M.member SearchBacklink <$> getM sGoals
  unless present (insertGoal SearchBacklink True)

insertCyclicGoals :: Reduction ()
insertCyclicGoals = do
  ctxt <- ask
  doCyclic <- gets (doCyclicInduction ctxt)
  when doCyclic $ do
    -- It is important to insert backlink search before minimzation so that
    -- backlinks are searched before minimization is done.
    insertSearchBacklink
    insertMinimize
