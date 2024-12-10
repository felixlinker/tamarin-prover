{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
module Theory.Constraint.Renaming
  ( renamedTimePoints
  , Renaming(..)
  , toSubst
  , prettyRenaming
  , applyR
  , DelayedRenaming
  , PartialRenaming(NoRenaming, Pure)
  , runRenaming
  , nonMonadicDomain
  , nonMonadicImage
  , nonMonadicRenaming
  , idRenaming
  , extendWith
  , Renamable(..)
  , mapVar
  , mapVarM
  , singleton
  ) where

import qualified Data.Map as M
import qualified Data.Set as S

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Term.LTerm
import Control.Monad (guard)
import Theory.Model.Rule (RuleACInst, getRuleRenaming, getRuleName)
import Term.Unification (SubstVFresh(..), WithMaude, LNSubstVFresh, LNSubst, Subst(..), unifyLNTerms, MaudeHandle, Apply(..))
import Theory.Model.Fact (LNFact, unifyLNFacts, Fact (factTag))
import Data.Maybe (mapMaybe, listToMaybe)
import Theory.Constraint.System.Constraints (Goal(..))
import Control.Monad.Trans.Reader (runReader)
import Text.PrettyPrint.Highlight (HighlightDocument, Document (vcat), operator_, space)

-- A Renaming is a substitution that always maps to variables.
data Renaming = Renaming
  { rsubst :: M.Map LVar LVar
  , img :: S.Set LVar }
  deriving ( Eq, Ord, Show, Generic, NFData, Binary )

instance HasFrees Renaming where
  foldFrees f (Renaming rsubst img) = foldFrees f rsubst <> foldFrees f img
  foldFreesOcc _ _ _ = mempty
  mapFrees f (Renaming rsubst img) = Renaming <$> mapFrees f rsubst <*> mapFrees f img

toSubst :: Renaming -> LNSubst
toSubst (Renaming r _) = Subst (M.map (LIT . Var) r)

prettyRenaming :: HighlightDocument d => Renaming -> d
prettyRenaming (M.toList . rsubst -> elems) = vcat (map showMapping elems)
  where
    showMapping (from, to) = prettyNodeId from <> space <> operator_ "~>" <> space <> prettyNodeId to

applyR :: Apply LNSubst a => Renaming -> a -> a
applyR (Renaming r _) = apply (Subst (M.map (LIT . Var) r) :: LNSubst)

idRenaming :: Renaming
idRenaming = Renaming M.empty S.empty

renamedTimePoints :: Renaming -> M.Map LVar LVar
renamedTimePoints (Renaming r _) = M.filterWithKey (\k _ -> lvarSort k == LSortNode) r

fromUnification :: HasFrees a => a -> a -> LNSubstVFresh -> Maybe Renaming
fromUnification a1 a2 = fmap toRenaming . M.foldrWithKey canonicalize (Just M.empty) . svMap
  where
    toRenaming :: M.Map LVar LVar -> Renaming
    toRenaming m =
      let m' = selfCompose m
      in Renaming m' (S.fromList $ M.elems m')

    rng1 = range a1
    rng2 = range a2

    -- TODO: This function could be replaced with couldBeRenaming
    canonicalize :: LVar -> VTerm Name LVar -> Maybe (M.Map LVar LVar) -> Maybe (M.Map LVar LVar)
    canonicalize v (termVar -> mtv) macc = do
      tv <- mtv
      aux tv <$> macc
      where
        aux tv
          | v `S.member` rng1 = M.insert v tv
          | v `S.member` rng2 = M.insert tv v
          | otherwise = error "illegal state"

    -- @selfCompose@ handles cases such as the following. Presume we want to
    -- rename variable x to variable y. One unifier could be [x->z, y->z].
    -- @canonicalize@ above will store this as [x->z,z->y] and @selfCompose@
    -- eliminates z.
    selfCompose :: M.Map LVar LVar -> M.Map LVar LVar
    -- @<> m@ keeps mappings that are already correct.
    selfCompose m = M.filterWithKey (\k _ -> k `S.member` rng1) (M.compose m m <> m)

    range :: HasFrees a => a -> S.Set LVar
    range = S.fromList . freesList

singleton :: LVar -> LVar -> Renaming
singleton v v' = Renaming (M.singleton v v') (S.singleton v')

mapVar :: LVar -> LVar -> Renaming -> Maybe Renaming
mapVar from to r@(Renaming m i)
  -- | If to is already in the image, it must be mapped by the same variable.
  --   Otherwise, this will not be a renaming.
  | to `S.member` i = do
    to' <- M.lookup from m
    guard (to == to')
    return r
  -- | If @from@ is already mapped, we cannot extend this renaming. It cannot
  --   map to @to@ either because this would have been caught by the previous
  --   guard.
  | M.member from m = Nothing
  | otherwise = Just $ Renaming (M.insert from to m) (S.insert to i)

type DelayedRenaming = WithMaude (Maybe Renaming)

noRenamingDelayed :: DelayedRenaming
noRenamingDelayed = return Nothing

updateDelayed :: DelayedRenaming -> Maybe Renaming -> DelayedRenaming
updateDelayed _ Nothing = noRenamingDelayed
updateDelayed dr (Just r) = maybe Nothing (mergeRenamings r) <$> dr

data PartialRenaming = NoRenaming | Pure Renaming | Monadic DelayedRenaming | Combined DelayedRenaming Renaming

nonMonadicDomain :: PartialRenaming -> S.Set LVar
nonMonadicDomain NoRenaming = S.empty
nonMonadicDomain (Pure (Renaming r _)) = M.keysSet r
nonMonadicDomain (Monadic _) = S.empty
nonMonadicDomain (Combined _ (Renaming r _)) = M.keysSet r

nonMonadicImage :: PartialRenaming -> S.Set LVar
nonMonadicImage NoRenaming = S.empty
nonMonadicImage (Pure r) = img r
nonMonadicImage (Monadic _) = S.empty
nonMonadicImage (Combined _ r) = img r

nonMonadicRenaming :: PartialRenaming -> Renaming
nonMonadicRenaming NoRenaming = idRenaming
nonMonadicRenaming (Pure r) = r
nonMonadicRenaming (Monadic _) = idRenaming
nonMonadicRenaming (Combined _ r) = r

runRenaming :: MaudeHandle -> PartialRenaming -> Maybe Renaming
runRenaming _ NoRenaming = Nothing
runRenaming _ (Pure m) = Just m
runRenaming mh (Monadic mm) = runReader mm mh
runRenaming mh (Combined dmr r) = do
  r' <- runReader dmr mh
  mergeRenamings r r'

tryMergeMaintaining :: DelayedRenaming -> Renaming -> Renaming -> PartialRenaming
tryMergeMaintaining dr r = maybe NoRenaming (Combined dr) . mergeRenamings r

tryMerge :: Renaming -> Renaming -> PartialRenaming
tryMerge r = maybe NoRenaming Pure . mergeRenamings r

instance Semigroup PartialRenaming where
  NoRenaming <> _ = NoRenaming
  _ <> NoRenaming = NoRenaming
  (Pure r) <> (Pure r') = tryMerge r r'
  (Pure r) <> (Combined mm r') = maybe NoRenaming (Combined mm) (mergeRenamings r r')
  (Combined mm r) <> (Pure r') = tryMergeMaintaining mm r r'
  (Pure r) <> (Monadic mm) = Combined mm r
  (Monadic mm) <> (Pure r) = Combined mm r
  (Combined mm r) <> (Combined mm' r') = tryMergeMaintaining (mm >>= updateDelayed mm') r r'
  (Monadic mm) <> (Combined mm' r) = Combined (mm >>= updateDelayed mm') r
  (Combined mm r) <> (Monadic mm') = Combined (mm >>= updateDelayed mm') r
  (Monadic mm) <> (Monadic mm') = Monadic (mm >>= updateDelayed mm')

instance Monoid PartialRenaming where
  mempty = Pure idRenaming

extendWith :: Functor f => PartialRenaming -> [f PartialRenaming] -> [f PartialRenaming]
extendWith NoRenaming _ = []
extendWith pr l = map (fmap (pr <>)) l

mapVarM :: LVar -> LVar -> PartialRenaming -> PartialRenaming
mapVarM _ _ NoRenaming = NoRenaming
mapVarM v1 v2 (Pure r) = maybe NoRenaming Pure (mapVar v1 v2 r)
mapVarM v1 v2 (Combined mm r) = maybe NoRenaming (Combined mm) (mapVar v1 v2 r)
mapVarM v1 v2 (Monadic mm) = Combined mm (singleton v1 v2)

class Renamable t where
  -- |  Compute a renaming from the first argument to the second. The renaming
  --    should ensure that whenever @Apply s t@, then @applyRenaming (t1 ~> t2) t1@
  --    is contained in @t2@.
  (~>) :: t -> t -> PartialRenaming

instance Renamable a => Renamable (Maybe a) where
  Nothing ~> Nothing = Pure idRenaming
  _ ~> Nothing = NoRenaming
  Nothing ~> _ = NoRenaming
  Just a1 ~> Just a2 = a1 ~> a2

instance (Renamable a, Renamable b) => Renamable (Either a b) where
  Left a1 ~> Left a2 = a1 ~> a2
  Right b1 ~> Right b2 = b1 ~> b2
  _ ~> _ = NoRenaming

-- TODO: This implementation is to easily support renaming AFNodes. This might
-- not work when there are multiple action facts associated with a node id. To
-- be checked! Potentially, we must explore all permutations (per action fact),
-- which could *potentially* return multiple renamings and would thus not fit
-- into this type class.
instance Renamable a => Renamable [a] where
  as1 ~> as2 = mconcat (zipWith (~>) as1 as2)

instance Renamable RuleACInst where
  r1 ~> r2 
    | getRuleName r1 /= getRuleName r2 = NoRenaming
    | otherwise = Monadic ((fromUnification r1 r2 =<<) <$> getRuleRenaming r1 r2)

instance Renamable LNFact where
  fa1 ~> fa2 
    | factTag fa1 /= factTag fa2 = NoRenaming
    | otherwise = Monadic (listToMaybe . mapMaybe (fromUnification fa1 fa2) <$> unifyLNFacts fa1 fa2)

instance Renamable LVar where
  v1 ~> v2
    | lvarSort v1 /= lvarSort v2 = NoRenaming
    | v1 == v2 = mempty
    | otherwise = Pure $ singleton v1 v2

instance Renamable LNTerm where
  (LIT (Var v)) ~> (LIT (Var w)) = v ~> w
  (LIT (Con x)) ~> (LIT (Con y))
    | x == y = mempty
    | otherwise = NoRenaming
  (LIT _) ~> (LIT _) = NoRenaming
  t1 ~> t2 = Monadic (listToMaybe . mapMaybe (fromUnification t1 t2) <$> unifyLNTerms t1 t2)

instance Renamable Goal where
  (ActionG v1 f1) ~> (ActionG v2 f2) = mapVarM v1 v2 (f1 ~> f2)
  (ChainG (c1, _) (p1, _)) ~> (ChainG (c2, _) (p2, _)) = (c1 ~> c2) <> (p1 ~> p2)
  (PremiseG (p1, _) f1) ~> (PremiseG (p2, _) f2) = (p1 ~> p2) <> (f1 ~> f2)
  (SplitG _) ~> (SplitG _) = mempty
  (DisjG _) ~> (DisjG _) = NoRenaming
  (SubtermG (ft1, st1)) ~> (SubtermG (ft2, st2)) = (ft1 ~> ft2) <> (st1 ~> st2)
  (Weaken _) ~> (Weaken _) = NoRenaming
  (Cut _) ~> (Cut _) = NoRenaming
  _ ~> _ = NoRenaming

mergeRenamings :: Renaming -> Renaming -> Maybe Renaming
mergeRenamings (Renaming m1 i1) (Renaming m2 i2) = do
  m' <- mergeMaps m1 m2
  return $ Renaming m' (S.union i1 i2)

mergeMaps :: (Ord k, Eq v) => M.Map k v -> M.Map k v -> Maybe (M.Map k v)
mergeMaps m1 m2 = M.fromAscList <$> go (M.toAscList m1) (M.toAscList m2)
  where
    go :: (Ord a, Eq b) => [(a, b)] -> [(a, b)] -> Maybe [(a, b)]
    go [] l2 = Just l2
    go l1 [] = Just l1
    go l1@((k1, v1):t1) l2@((k2, v2):t2)
      | k1 == k2 && v1 == v2 = ((k1,v1):) <$> go t1 t2
      | k1 < k2 = ((k1, v1):) <$> go t1 l2
      | k2 < k1 = ((k2, v2):) <$> go l1 t2
      | otherwise = Nothing
