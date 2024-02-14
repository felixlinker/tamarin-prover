{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE TupleSections      #-}
module Theory.Constraint.System.Inclusion
  ( UpTo
  , prettyUpTo
  , ProgressingVars
  , pvProgresses
  , pvPreserves
  , getCycleRenamingsOnPath
  , getCycleRenamingOnPath
  , canCloseCycle ) where

import Data.Label (mkLabels)
import qualified Extension.Data.Label as L
import qualified Data.Set as S
import Theory.Constraint.System
import Term.LTerm
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Text.PrettyPrint.Highlight (HighlightDocument, comma)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Term.Maude.Process (WithMaude, MaudeHandle)
import Theory.Constraint.Renaming
import Term.Substitution (LNSubst, Subst (sMap))
import qualified Data.Map as M
import Data.List ( intersperse, groupBy )
import Text.PrettyPrint.Class (fsep)
import Control.Monad.Reader (runReader)
import Control.Monad
import GHC.OldList (permutations)
import Theory.Model.Rule
import Data.Maybe (mapMaybe, fromMaybe)
import Theory.Model.Signature (sigmMaudeHandle)
import GHC.List (uncons)

type UpTo = S.Set LNGuarded

data ProgressingVars = ProgressingVars
  { _pvProgresses :: S.Set NodeId
    -- ^ To be understood as <. Hence, is subset of pvPreserves.
  , _pvPreserves :: S.Set NodeId
    -- ^ to be understood as <=.
  }
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''ProgressingVars])

prettyUpTo :: HighlightDocument d => UpTo -> d
prettyUpTo = fsep . intersperse comma . map prettyGuarded . S.toList

-- |  @Nothing@ is an incorrect renaming, @Just S.Empty@ is a correct renaming,
--    and everything else a potentially correct renaming.
type RenamingUpToT = MaybeT WithMaude UpTo
type RenamingUpToWithVarsT = MaybeT WithMaude (Renaming LNSubst, UpTo, ProgressingVars)

computeRenamingUpTo :: RenamingUpToWithVarsT -> MaudeHandle -> Maybe (Renaming LNSubst, UpTo, ProgressingVars)
computeRenamingUpTo mr = runReader $ runMaybeT mr

-- TODO: Handle last
isSubSysUpTo :: System -> System -> MaybeRenaming LNSubst -> RenamingUpToT
isSubSysUpTo smaller larger renamingT = do
  renaming <- renamingT
  guard (applyRenaming renaming (L.get sEdges smaller) `S.isSubsetOf` L.get sEdges larger)
  guard (applyRenaming renaming (S.map lessAtomToEdge $ L.get sLessAtoms smaller) `S.isSubsetOf` S.fromList (transitiveLessRel larger))
  let smallerFormulas = applyRenaming renaming (L.get sSolvedFormulas smaller <> L.get sFormulas smaller)
  let largerFormulas = L.get sSolvedFormulas larger <> L.get sFormulas larger
  -- guard (applyRenaming renaming (L.get sSolvedFormulas smaller) `S.isSubsetOf` L.get sSolvedFormulas larger)
  let diffFormulas = smallerFormulas `S.difference` largerFormulas
  return diffFormulas

isProgressingAndSubSysUpTo :: System -> System -> MaybeRenaming LNSubst -> RenamingUpToWithVarsT
isProgressingAndSubSysUpTo smaller larger rM =  do
  r <- rM
  let withVars = getProgressingVars larger (renamedTimePoints r)
  guard (not $ S.null $ L.get pvProgresses withVars)
  upTo <- isSubSysUpTo smaller larger rM
  return (r, upTo, withVars)

allLoopRenamings :: ProofContext -> System -> System -> [MaybeRenaming LNSubst]
allLoopRenamings ctxt smaller larger =
  let nidsCycleTgt = gatherRules $ getRenamableNodes smaller
      nidsCycleCnd = gatherRules $ getRenamableNodes larger
      -- TODO: Apply heuristic whether to search for renamings
      -- NOTE: Idea; I could memorize progress-candidates
  in map isRenaming $ renamingsByRule nidsCycleTgt nidsCycleCnd [idRenaming]
  where
    domSmaller :: S.Set (VTerm Name LVar)
    domSmaller = S.fromList $ map (LIT . Var) $ frees smaller

    isRenaming :: MaybeRenaming LNSubst -> MaybeRenaming LNSubst
    isRenaming rM = do
      r <- rM
      guard (not $ any (`S.member` domSmaller) (M.elems $ sMap $ L.get giSubst r))
      return r

    renamingsByRule :: [[Node]] -> [[Node]] -> [MaybeRenaming LNSubst] -> [MaybeRenaming LNSubst]
    renamingsByRule _ _ []                 = []
    renamingsByRule [] [] acc              = acc
    renamingsByRule [] (_:_) acc           = acc
    renamingsByRule (_:_) [] _             = []
    renamingsByRule (ns1:t1) (ns2:t2) acc  =
      let ruleRenamings = map (allRenamings ns1 ns2) acc
      in  foldl rec [] ruleRenamings
      where
        rec :: [MaybeRenaming LNSubst] -> [MaybeRenaming LNSubst] -> [MaybeRenaming LNSubst]
        rec foldAcc ruleRenamings = foldAcc ++ renamingsByRule t1 t2 ruleRenamings

    allRenamings :: [Node] -> [Node] -> MaybeRenaming LNSubst -> [MaybeRenaming LNSubst]
    allRenamings ns1 ns2 acc = if length ns1 > length ns2
      then []
      else map ((~><~ acc) . (ns1 ~>)) (permutations ns2)

    forSys :: System -> NodeId -> Node
    forSys sys nid = Node nid $ L.get sNodes sys M.! nid

    getRenamableNodes :: System -> S.Set Node
    getRenamableNodes sys = S.map (forSys sys) (getLoopNodes ctxt sys)

    gatherRules :: S.Set Node -> [[Node]]
    gatherRules = groupBy (\n1 n2 -> get_rInfo n1 == get_rInfo n2) . S.toAscList
      where get_rInfo = L.get rInfo . nrule

isContainedInModRenamingUpTo :: ProofContext -> System -> System -> RenamingUpToWithVarsT
isContainedInModRenamingUpTo ctxt smaller larger = msum $ map (isProgressingAndSubSysUpTo smaller larger) (allLoopRenamings ctxt smaller larger)

getCycleRenamingsOnPath :: ProofContext -> [System] -> [(Renaming LNSubst, UpTo, SystemId, ProgressingVars)]
getCycleRenamingsOnPath _ [] = []
getCycleRenamingsOnPath ctx (leaf:candidates) = mapMaybe tryRenaming candidates
  where
    hnd = L.get sigmMaudeHandle $ L.get pcSignature ctx
    tryRenaming inner = do
      (r, upTo, progressing) <- computeRenamingUpTo (isContainedInModRenamingUpTo ctx inner leaf) hnd
      return (r, upTo, L.get sId inner, progressing)

getCycleRenamingOnPath :: ProofContext -> [System] -> Maybe (Renaming LNSubst, UpTo, SystemId, ProgressingVars)
getCycleRenamingOnPath ctx = peak . getCycleRenamingsOnPath ctx
  where peak = (fst <$>) . uncons

canCloseCycle :: ProofContext -> [System] -> Maybe (SystemId, ProgressingVars)
canCloseCycle ctx p = do
  (_, upTo, sid, progressingVars) <- getCycleRenamingOnPath ctx p
  guard (S.null upTo)
  return (sid, progressingVars)

getProgressingVars :: System -> [(LVar, LVar)] -> ProgressingVars
getProgressingVars sys renamings =
  let srcs = S.fromList $ map snd renamings
      tgts = S.fromList $ map fst renamings
      lessRel = concat $ lessRelTopoSortedAsc sys
      progressing = S.intersection tgts $ go srcs lessRel
  in ProgressingVars progressing (M.keysSet $ L.get sNodes sys) where
    go :: S.Set NodeId -> [(NodeId, NodeId)] -> S.Set NodeId
    go acc [] = acc
    go acc ((from, to):es) = go (if from `S.member` acc then S.insert to acc else acc) es

transitiveLessRel :: System -> [(NodeId, NodeId)]
transitiveLessRel se = collect $ go M.empty $ concat $ lessRelTopoSortedAsc se
  where
    collect :: M.Map NodeId (S.Set NodeId) -> [(NodeId, NodeId)]
    collect = concatMap (\(k, vs) -> map (,k) $ S.toList vs) . M.toList

    go :: M.Map NodeId (S.Set NodeId) -> [(NodeId, NodeId)] -> M.Map NodeId (S.Set NodeId)
    go m [] = m
    go m ((s,t):es) =
      let canReachS = fromMaybe S.empty $ M.lookup s m
          newAcc = M.alter (Just . S.union canReachS . maybe (S.singleton s) (S.insert s)) t m
      in go newAcc es

lessRelTopoSortedAsc :: System -> [[(NodeId, NodeId)]]
lessRelTopoSortedAsc = go . S.fromList . rawLessRel
  where
    go :: S.Set (NodeId, NodeId) -> [[(NodeId, NodeId)]]
    go s  | S.null s  = []
          | otherwise =
            let noOutgoing = S.map fst s S.\\ S.map snd s
                (mins, rest) = S.partition ((`S.member` noOutgoing) . fst) s
            in  if   S.null mins
                -- TODO: Can be called on cyclic graph, e.g., when there
                -- are cyclic timepoints. This is then also a
                -- contradiction, but I should establish this invariant.
                then error "not a DAG"
                else S.toList mins : go rest
