{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveAnyClass     #-}
module Theory.Constraint.System.Inclusion
  ( UpTo
  , upToToFormulas
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
import Term.Substitution (LNSubst)
import qualified Data.Map as M
import Data.List ( intersperse, groupBy )
import Text.PrettyPrint.Class (fsep)
import Control.Monad.Reader (runReader)
import Control.Monad
import GHC.OldList (permutations)
import Theory.Model.Rule
import Data.Maybe (mapMaybe)
import Theory.Model.Signature (sigmMaudeHandle)
import GHC.List (uncons)

type UpTo = S.Set (Either LNGuarded LessAtom)

data ProgressingVars = ProgressingVars
  { _pvProgresses :: S.Set NodeId
    -- ^ To be understood as <. Hence, is subset of pvPreserves.
  , _pvPreserves :: S.Set NodeId
    -- ^ to be understood as <=.
  }
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''ProgressingVars])

upToToFormulas :: UpTo -> [LNGuarded]
upToToFormulas = map toFormula . S.toList
  where
    toFormula :: Either LNGuarded LessAtom -> LNGuarded
    toFormula = either id lessAtomToFormula

prettyUpTo :: HighlightDocument d => UpTo -> d
prettyUpTo = fsep . intersperse comma . map prettyGuarded . upToToFormulas

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
  let diffLessAtoms = applyRenaming renaming (L.get sLessAtoms smaller) `S.difference` L.get sLessAtoms larger
  let smallerFormulas = applyRenaming renaming (L.get sSolvedFormulas smaller <> L.get sFormulas smaller)
  let largerFormulas = L.get sSolvedFormulas larger <> L.get sFormulas larger
  -- guard (applyRenaming renaming (L.get sSolvedFormulas smaller) `S.isSubsetOf` L.get sSolvedFormulas larger)
  let diffFormulas = smallerFormulas `S.difference` largerFormulas
  return $ S.map Right diffLessAtoms <> S.map Left diffFormulas

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
  in  renamingsByRule nidsCycleTgt nidsCycleCnd [idRenaming]
  where
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
      sorting = topologicalSortingAsc $ S.fromList $ rawLessRel sys
      progressing = S.intersection tgts $ go srcs sorting
  in ProgressingVars progressing (M.keysSet $ L.get sNodes sys) where
    go :: S.Set NodeId -> [(NodeId, NodeId)] -> S.Set NodeId
    go acc [] = acc
    go acc ((from, to):es) = go (if from `S.member` acc then S.insert to acc else acc) es

topologicalSortingAsc :: S.Set (NodeId, NodeId) -> [(NodeId, NodeId)]
topologicalSortingAsc s
  | S.null s  = []
  | otherwise = let noOutgoing = S.map fst s S.\\ S.map snd s
                    (mins, rest) = S.partition ((`S.member` noOutgoing) . fst) s
                in  if   S.null mins
                    -- TODO: Can be called on cyclic graph, e.g., when there
                    -- are cyclic timepoints. This is then also a
                    -- contradiction, but I should establish this invariant.
                    then error "not a DAG"
                    else S.toList mins ++ topologicalSortingAsc rest
