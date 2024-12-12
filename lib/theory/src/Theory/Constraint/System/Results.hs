{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
module Theory.Constraint.System.Results
  ( Contradiction(..)
  , ContradictionAccumulator(..)
  , fromContradictionResult
  , Result(..)
  , equivResult
  , prettyContradiction
  , prettyResult ) where

import GHC.Generics (Generic)
import Data.Binary
import Control.DeepSeq
import Theory.Proof.Cyclic
import Theory.Model
import Text.PrettyPrint.Highlight (HighlightDocument, keyword_, Document (sep, text), doubleQuotes, emptyDoc)
import Theory.Text.Pretty (lineComment_, closedComment,(<->))


-- | Reasons why a constraint 'System' can be contradictory.
data Contradiction =
    CyclicTimePoints               -- ^ The paths are cyclic.
  | SubtermCyclic                  -- ^ The subterm predicates form a cycle
  | NonNormalTerms                 -- ^ Has terms that are not in normal form.
  -- | NonLastNode                    -- ^ Has a non-silent node after the last node.
  | ForbiddenExp                   -- ^ Forbidden Exp-down rule instance
  | ForbiddenBP                    -- ^ Forbidden bilinear pairing rule instance
  | ForbiddenKD                    -- ^ has forbidden KD-fact
  | ImpossibleChain                -- ^ has impossible chain
  | ForbiddenChain                 -- ^ has forbidden chain
  | NonInjectiveFactInstance (NodeId, NodeId, NodeId)
    -- ^ Contradicts that certain facts have unique instances.
  | IncompatibleEqs                -- ^ Incompatible equalities.
  | FormulasFalse                  -- ^ False in formulas
  | SuperfluousLearn LNTerm NodeId -- ^ A term is derived both before and after a learn
  | NodeAfterLast (NodeId, NodeId) -- ^ There is a node after the last node.
  | Cyclic BackLink
    -- ^ Cyclic proof
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- |  Needed for definition of type reduction. Combine contradictions by simply
--    picking an arbitrary one.
instance Semigroup Contradiction where
  c1 <> _ = c1

instance HasFrees Contradiction where
  foldFrees f (NonInjectiveFactInstance ns) = foldFrees f ns
  foldFrees f (SuperfluousLearn t n) = foldFrees f t <> f n
  foldFrees f (NodeAfterLast ns) = foldFrees f ns
  foldFrees f (Cyclic bl) = foldFrees f bl
  foldFrees _ _ = mempty
  foldFreesOcc _ _ _ = mempty
  mapFrees f (NonInjectiveFactInstance ns) = NonInjectiveFactInstance <$> mapFrees f ns
  mapFrees f (SuperfluousLearn t n) = SuperfluousLearn <$> mapFrees f t <*> mapFrees f n
  mapFrees f (NodeAfterLast ns) = NodeAfterLast <$> mapFrees f ns
  mapFrees f (Cyclic bl) = Cyclic <$> mapFrees f bl
  mapFrees _ c = pure c

data ContradictionAccumulator = Simple | FromCyclic CyclicProof
  deriving ( Eq, Ord, Show, Generic, NFData, Binary )

fromContradiction :: Contradiction -> ContradictionAccumulator
fromContradiction (Cyclic bl) = FromCyclic (toProof bl)
fromContradiction _ = Simple

instance Semigroup ContradictionAccumulator where
  Simple <> acc = acc
  acc <> Simple = acc
  FromCyclic prf <> FromCyclic prf' = FromCyclic (prf <> prf')

data Result a =
    Solved
  -- ^ A dependency graph was found.
  | Contradictory (Maybe a)
  -- ^ A contradiction could be derived, possibly with a reason. The single
  --    formula constraint in the system.
  | Unfinishable
  -- ^ The proof cannot be finished (due to reducible operators in subterms or
  --   because a solution was found after weakening).
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

instance Functor Result where
  fmap _ Solved = Solved
  fmap _ Unfinishable = Unfinishable
  fmap f (Contradictory c) = Contradictory (f <$> c)

fromContradictionResult :: Result Contradiction -> Result ContradictionAccumulator
fromContradictionResult = fmap fromContradiction

instance Semigroup a => Semigroup (Result a) where
  Solved <> _ = Solved
  _ <> Solved = Solved
  Unfinishable <> _ = Unfinishable
  _ <> Unfinishable = Unfinishable
  Contradictory c <> Contradictory c' = Contradictory (c <> c')

instance HasFrees (Result Contradiction) where
  foldFrees f (Contradictory (Just c)) = foldFrees f c
  foldFrees _ _ = mempty
  foldFreesOcc _ _ _ = mempty
  mapFrees f (Contradictory r) = Contradictory <$> mapFrees f r
  mapFrees _ r = pure r

equivResult :: Result a -> Result a -> Bool
equivResult (Contradictory _) (Contradictory _) = True
equivResult Solved Solved = True
equivResult Unfinishable Unfinishable = True
equivResult _ _ = False

prettyContradiction :: Document d => Contradiction -> d
prettyContradiction contra = case contra of
    CyclicTimePoints             -> text "cyclic"
    SubtermCyclic                -> text "contradictory subterm store"
    IncompatibleEqs              -> text "incompatible equalities"
    NonNormalTerms               -> text "non-normal terms"
    ForbiddenExp                 -> text "non-normal exponentiation rule instance"
    ForbiddenBP                  -> text "non-normal bilinear pairing rule instance"
    ForbiddenKD                  -> text "forbidden KD-fact"
    ForbiddenChain               -> text "forbidden chain"
    ImpossibleChain              -> text "impossible chain"
    NonInjectiveFactInstance cex -> text $ "non-injective facts " ++ show cex
    Cyclic (BackLink (_, sid) _ _) -> text $ "cyclic backlink to CS id " ++ show sid
    FormulasFalse                -> text "from formulas"
    SuperfluousLearn m v         ->
        doubleQuotes (prettyLNTerm m) <->
        text "derived before and after" <->
        doubleQuotes (prettyNodeId v)
    NodeAfterLast (i,j)          ->
        text $ "node " ++ show j ++ " after last node " ++ show i

prettyResult :: HighlightDocument d => Result Contradiction -> d
prettyResult Solved = keyword_ "SOLVED" <-> lineComment_ "trace found"
prettyResult Unfinishable = keyword_ "UNFINISHABLE" <-> lineComment_ "reducible operator in subterm or solved after weakening"
prettyResult (Contradictory reason) = sep
  [ keyword_ "contradiction"
  , maybe emptyDoc (closedComment . prettyContradiction) reason ]
