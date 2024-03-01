{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Types representing constraints.
module Theory.Constraint.System.Constraints (
  -- * Guarded formulas
    module Theory.Constraint.System.Guarded

  -- * Graph constraints
  , NodePrem
  , NodeConc
  , Edge(..)
  , Reason(..)

  -- ** Less Atoms
  , LessAtom(..)
  , laSmaller
  , laLarger
  , laReason
  , lessAtomFromEdge
  , lessAtomToEdge
  , getLessRel

  -- * Goal constraints
  , Goal(..)
  , UpTo
  , WeakenEl(..)
  , isActionGoal
  , isStandardActionGoal
  , isSubtermGoal
  , isPremiseGoal
  , isChainGoal
  , isSplitGoal
  , isDisjGoal

  -- ** Pretty-printing
  , prettyNode
  , prettyNodePrem
  , prettyNodeConc
  , prettyEdge
  , prettyLess
  , prettyGoal
  ) where
import           GHC.Generics (Generic)
import           Data.Binary
import           Data.Data
import           Data.Label                           (mkLabels)
import qualified Data.Set as S

import           Control.DeepSeq

import           Text.PrettyPrint.Class
import           Text.Unicode

import           Logic.Connectives
import           Theory.Constraint.System.Guarded
import           Theory.Model
import           Theory.Text.Pretty
import           Theory.Tools.EquationStore
import Data.List (intersperse)

------------------------------------------------------------------------------
-- Graph part of a sequent                                                  --
------------------------------------------------------------------------------

-- | A premise of a node.
type NodePrem = (NodeId, PremIdx)

-- | A conclusion of a node.
type NodeConc = (NodeId, ConcIdx)

-- | A labeled edge in a derivation graph.
data Edge = Edge {
      eSrc :: NodeConc
    , eTgt :: NodePrem
    }
  deriving (Show, Ord, Eq, Data, Typeable, Generic, NFData, Binary)

-- | A reason to explain the less
-- | Order is from the most important to the least important 
-- TODO: Is KeepWeakened in right order?
data Reason = Formula | InjectiveFacts | Fresh | KeepWeakened | Adversary | NormalForm
      deriving (Ord, Eq, Data, Typeable, Generic, NFData, Binary)

-- Instances
------------
instance Show Reason where
    show Fresh              = "fresh value"
    show Formula            = "formula"
    show InjectiveFacts     = "injective facts"
    show KeepWeakened       = "keep order of weakened nodes"
    show NormalForm         = "normal form condition"
    show Adversary          = "adversary"

instance Apply LNSubst Reason where
    apply = const id

instance HasFrees Reason where
    foldFrees = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees  = const pure
    
instance Apply LNSubst Edge where
    apply subst (Edge from to) = Edge (apply subst from) (apply subst to)

instance HasFrees Edge where
    foldFrees f (Edge x y) = foldFrees f x `mappend` foldFrees f y
    foldFreesOcc  f c (Edge x y) = foldFreesOcc f ("edge":c) (x, y)
    mapFrees  f (Edge x y) = Edge <$> mapFrees f x <*> mapFrees f y

-- | A *⋖* constraint between 'NodeId's.
data LessAtom = LessAtom
  { _laSmaller :: NodeId
  , _laLarger :: NodeId
  , _laReason :: Reason }
  deriving( Show, Generic, NFData, Binary )

$(mkLabels [''LessAtom])

instance Eq LessAtom where
  (LessAtom s1 l1 _) == (LessAtom s2 l2 _) = s1 == s2 && l1 == l2

instance Ord LessAtom where
  compare (LessAtom s1 l1 _) (LessAtom s2 l2 _) = compare (s1, l1) (s2, l2)

lessAtomFromEdge :: Reason -> Edge -> LessAtom
lessAtomFromEdge r (Edge (src, _) (tgt, _)) = LessAtom src tgt r

lessAtomToEdge :: LessAtom -> (NodeId, NodeId)
lessAtomToEdge (LessAtom s t _) = (s, t)

-- | Gets the relation of the lesses
getLessRel :: [LessAtom] -> [(NodeId, NodeId)]
getLessRel = map lessAtomToEdge

instance Apply LNSubst LessAtom where
    apply subst (LessAtom smaller larger r) = LessAtom (apply subst smaller) (apply subst larger) r

instance HasFrees LessAtom where
    foldFrees f (LessAtom s l _) = foldFrees f s <> foldFrees f l
    foldFreesOcc f c (LessAtom s l _) = foldFreesOcc f ("lessAtom":c) (s, l)
    mapFrees f (LessAtom s l r) = LessAtom <$> mapFrees f s <*> mapFrees f l <*> pure r

------------------------------------------------------------------------------
-- Goals
------------------------------------------------------------------------------

type UpTo = S.Set LNGuarded

data WeakenEl = WeakenNode NodeId | WeakenGoal Goal | WeakenEdge Edge
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A 'Goal' denotes that a constraint reduction rule is applicable, which
-- might result in case splits. We either use a heuristic to decide what goal
-- to solve next or leave the choice to user (in case of the interactive UI).
data Goal =
       ActionG LVar LNFact
       -- ^ An action that must exist in the trace.
     | ChainG NodeConc NodePrem
       -- ^ A destruction chain. ConcIdx of NodeConc will always be 0.
       --   This invariant is estalished by @insertGoal@.
     | PremiseG NodePrem LNFact
       -- ^ A premise that must have an incoming direct edge.
     | SplitG SplitId
       -- ^ A case split over equalities.
     | DisjG (Disj LNGuarded)
       -- ^ A case split over a disjunction.
     | SubtermG (LNTerm, LNTerm)
       -- ^ A split of a Subterm which is in SubtermStore -> _subterms
     | Weaken WeakenEl
     | Cut UpTo
     deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- Indicators
-------------

isActionGoal :: Goal -> Bool
isActionGoal (ActionG _ _) = True
isActionGoal _             = False

isStandardActionGoal :: Goal -> Bool
isStandardActionGoal (ActionG _ fa) = not (isKUFact fa)
isStandardActionGoal _              = False

isPremiseGoal :: Goal -> Bool
isPremiseGoal (PremiseG _ _) = True
isPremiseGoal _              = False

isChainGoal :: Goal -> Bool
isChainGoal (ChainG _ _) = True
isChainGoal _            = False

isSplitGoal :: Goal -> Bool
isSplitGoal (SplitG _) = True
isSplitGoal _          = False

isDisjGoal :: Goal -> Bool
isDisjGoal (DisjG _) = True
isDisjGoal _         = False

isSubtermGoal :: Goal -> Bool
isSubtermGoal (DisjG _) = True
isSubtermGoal _         = False



-- Instances
------------

instance HasFrees WeakenEl where
  foldFrees f (WeakenNode nid) = foldFrees f nid
  foldFrees f (WeakenGoal g) = foldFrees f g
  foldFrees f (WeakenEdge e) = foldFrees f e

  foldFreesOcc _ _ _ = mempty

  mapFrees f (WeakenNode nid) = WeakenNode <$> mapFrees f nid
  mapFrees f (WeakenGoal g) = WeakenGoal <$> mapFrees f g
  mapFrees f (WeakenEdge e) = WeakenEdge <$> mapFrees f e

instance Apply LNSubst WeakenEl where
  apply subst (WeakenNode nid) = WeakenNode (apply subst nid)
  apply subst (WeakenGoal g) = WeakenGoal (apply subst g)
  apply subst (WeakenEdge e) = WeakenEdge (apply subst e)

instance HasFrees Goal where
    foldFrees f goal = case goal of
        ActionG i fa  -> foldFrees f i <> foldFrees f fa
        PremiseG p fa -> foldFrees f p <> foldFrees f fa
        ChainG c p    -> foldFrees f c <> foldFrees f p
        SplitG i      -> foldFrees f i
        DisjG x       -> foldFrees f x
        SubtermG p    -> foldFrees f p
        Weaken el     -> foldFrees f el
        Cut phis      -> foldFrees f phis

    foldFreesOcc  f c goal = case goal of
        ActionG i fa -> foldFreesOcc f ("ActionG":c) (i, fa)
        ChainG co p  -> foldFreesOcc f ("ChainG":c)  (co, p)
        _            -> mempty

    mapFrees f goal = case goal of
        ActionG i fa  -> ActionG  <$> mapFrees f i <*> mapFrees f fa
        PremiseG p fa -> PremiseG <$> mapFrees f p <*> mapFrees f fa
        ChainG c p    -> ChainG   <$> mapFrees f c <*> mapFrees f p
        SplitG i      -> SplitG   <$> mapFrees f i
        DisjG x       -> DisjG    <$> mapFrees f x
        SubtermG p    -> SubtermG <$> mapFrees f p
        Weaken el     -> Weaken <$> mapFrees f el
        Cut upTo      -> Cut <$> mapFrees f upTo

instance Apply LNSubst Goal where
    apply subst goal = case goal of
        ActionG i fa  -> ActionG  (apply subst i) (apply subst fa)
        PremiseG p fa -> PremiseG (apply subst p) (apply subst fa)
        ChainG c p    -> ChainG   (apply subst c) (apply subst p)
        SplitG i      -> SplitG   (apply subst i)
        DisjG x       -> DisjG    (apply subst x)
        SubtermG p    -> SubtermG (apply subst p)
        Weaken el     -> Weaken   (apply subst el)
        Cut phis      -> Cut      (apply subst phis)


------------------------------------------------------------------------------
-- Pretty printing                                                          --
------------------------------------------------------------------------------
-- | Pretty print a reason
prettyReason :: HighlightDocument d => Reason -> d
prettyReason r = text $ "induced by " ++ show r
    
-- | Pretty print a node.
prettyNode :: HighlightDocument d => (NodeId, RuleACInst) -> d
prettyNode (v,ru) = prettyNodeId v <> colon <-> prettyRuleACInst ru

-- | Pretty print a node conclusion.
prettyNodeConc :: HighlightDocument d => NodeConc -> d
prettyNodeConc (v, ConcIdx i) = parens (prettyNodeId v <> comma <-> int i)

-- | Pretty print a node premise.
prettyNodePrem :: HighlightDocument d => NodePrem -> d
prettyNodePrem (v, PremIdx i) = parens (prettyNodeId v <> comma <-> int i)

-- | Pretty print a edge as @src >-i--j-> tgt@.
prettyEdge :: HighlightDocument d => Edge -> d
prettyEdge (Edge c p) =
    prettyNodeConc c <-> operator_ ">-->" <-> prettyNodePrem p

-- | Pretty print a less-atom as @src < tgt@.
prettyLess :: HighlightDocument d => LessAtom -> d
prettyLess (LessAtom i j r) = prettyNAtom (Less (varTerm i) (varTerm j)) <> colon <-> prettyReason r



solve :: HighlightDocument d => d -> d
solve inner = keyword_ "solve(" <-> inner <-> keyword_ ")"

weaken :: HighlightDocument d => String -> d -> d
weaken what inner = keyword_ ("weaken " ++ what ++ "(") <-> inner <-> keyword_ ")"

cut :: HighlightDocument d => d -> d
cut inner = keyword_ "cut(" <-> inner <-> keyword_ ")"

prettyUpTo :: HighlightDocument d => UpTo -> d
prettyUpTo = fsep . intersperse comma . map prettyGuarded . S.toList

-- | Pretty print a goal.
prettyGoal :: HighlightDocument d => Goal -> d
prettyGoal (ActionG i fa) = solve $ prettyNAtom (Action (varTerm i) fa)
prettyGoal (ChainG c p)   =
    solve $ prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p
prettyGoal (PremiseG (i, (PremIdx v)) fa) =
    -- Note that we can use "▷" for conclusions once we need them.
    solve $ prettyLNFact fa <-> text ("▶" ++ subscript (show v)) <-> prettyNodeId i
    -- prettyNodePrem p <> brackets (prettyLNFact fa)
prettyGoal (DisjG (Disj []))  = solve $ text "Disj" <-> operator_ "(⊥)"
prettyGoal (DisjG (Disj gfs)) = solve $ fsep $
    punctuate (operator_ "  ∥") (map (nest 1 . parens . prettyGuarded) gfs)
    -- punctuate (operator_ " |") (map (nest 1 . parens . prettyGuarded) gfs)
prettyGoal (SplitG x) =
    solve $ text "splitEqs" <> parens (text $ show (unSplitId x))
prettyGoal (SubtermG (l,r)) =
    solve $ prettyLNTerm l <-> operator_ "⊏" <-> prettyLNTerm r
prettyGoal (Cut ut) = cut $ prettyUpTo ut
prettyGoal (Weaken (WeakenNode i)) = weaken "node" $ prettyNodeId i
prettyGoal (Weaken (WeakenGoal g)) = weaken "goal" $ prettyGoal g
prettyGoal (Weaken (WeakenEdge e)) = weaken "edge" $ prettyEdge e
