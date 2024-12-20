{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
--
-- AC unification based on maude and free unification.
module Term.Unification (
  -- * Variable substitutions
    LVarSubst
  , toVarSubst
  , mergeLVarSubsts

  -- * Unification modulo AC
  , unifyLTerm
  , unifyLNTerm
  , unifyLNTerms
  , unifiableLNTerms
  , unifyLTermOriented
  , unifyLNTermOriented

  , unifyLTermFactored
  , unifyLNTermFactored

  -- * Unification without AC
  , unifyLTermNoAC
  , unifyLNTermNoAC
  , unifiableLNTermsNoAC
  , eqLNTerms
  , eqSubsts

  , unifyLTermFactoredNoAC
  , unifyLNTermFactoredNoAC

  -- * matching modulo AC
  -- ** Constructing matching problems
  , matchLVar

  -- ** Solving matching problems
  , solveMatchLTerm
  , solveMatchLNTerm

  -- * Handles to a Maude process
  , MaudeHandle
  , WithMaude
  , startMaude
  , getMaudeStats
  , mhMaudeSig
  , mhFilePath

  -- * Maude signatures
  , MaudeSig
  , enableDH
  , enableBP
  , enableMSet
  , enableNat
  , enableXor
  , enableDiff
  , minimalMaudeSig
  , enableDiffMaudeSig
  , dhMaudeSig
  , natMaudeSig
  , bpMaudeSig
  , xorMaudeSig
  , msetMaudeSig
  , pairMaudeSig
  , symEncMaudeSig
  , asymEncMaudeSig
  , signatureMaudeSig
  , pairDestMaudeSig
  , symEncDestMaudeSig
  , asymEncDestMaudeSig
  , signatureDestMaudeSig
  , locationReportMaudeSig
  , revealSignatureMaudeSig
  , hashMaudeSig
  , rrulesForMaudeSig
  , stFunSyms
  , funSyms
  , stRules
  , irreducibleFunSyms
  , reducibleFunSyms
  , noEqFunSyms
  , addFunSym
  , addCtxtStRule

  -- * Convenience exports
  , module Term.Substitution
  , module Term.Rewriting.Definitions
) where

import           Control.Monad
import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Map (Map)

import           System.IO.Unsafe (unsafePerformIO)


import           Term.Term.FunctionSymbols
import           Term.Rewriting.Definitions
import           Term.Substitution
import qualified Term.Maude.Process as UM
import           Term.Maude.Process
                   (MaudeHandle, WithMaude, startMaude, getMaudeStats, mhMaudeSig, mhFilePath)
import           Term.Maude.Signature
import Data.Maybe (isJust, mapMaybe)

-- Unification modulo AC
----------------------------------------------------------------------

-- | @unifyLTerm sortOf eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLTermFactored :: (IsConst c)
                   => (c -> LSort)
                   -> [Equal (LTerm c)]
                   -> WithMaude (LSubst c, [SubstVFresh c LVar])
unifyLTermFactored sortOf eqs = reader $ \h -> do
    solve h $ execRWST unif sortOf M.empty
  where
    unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
    solve _ Nothing         = (emptySubst, [])
    solve _ (Just (m, []))  = (substFromMap m, [emptySubstVFresh])
    solve h (Just (m, leqs)) =
        (subst, unsafePerformIO (UM.unifyViaMaude h sortOf $
                                     map (applyVTerm subst <$>) leqs))
      where subst = substFromMap m


-- | @unifyLTerm sortOf eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLNTermFactored :: [Equal LNTerm]
                    -> WithMaude (LNSubst, [SubstVFresh Name LVar])
unifyLNTermFactored = unifyLTermFactored sortOfName

-- | @unifyLNTerm eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLTerm :: (IsConst c)
           => (c -> LSort)
           -> [Equal (LTerm c)]
           -> WithMaude [SubstVFresh c LVar]
unifyLTerm sortOf eqs = flattenUnif <$> unifyLTermFactored sortOf eqs

type LVarSubst = M.Map LVar LVar

toVarSubst :: LSubst c -> Maybe LVarSubst
toVarSubst = traverse termVar . sMap

mergeLVarSubsts :: LVarSubst -> LVarSubst -> Maybe LVarSubst
mergeLVarSubsts m1 m2 = M.fromAscList <$> go (M.toAscList m1) (M.toAscList m2)
  where
    go :: (Ord a, Eq b) => [(a, b)] -> [(a, b)] -> Maybe [(a, b)]
    go [] l2 = Just l2
    go l1 [] = Just l1
    go l1@((k1, v1):t1) l2@((k2, v2):t2)
      | k1 == k2 && v1 == v2 = ((k1,v1):) <$> go t1 t2
      | k1 < k2 = ((k1, v1):) <$> go t1 l2
      | k2 < k1 = ((k2, v2):) <$> go l1 t2
      | otherwise = Nothing

composeOrientedUnifs :: (IsConst c) => S.Set LVar -> S.Set LVar -> (LSubst c, [LSubstVFresh c]) -> Maybe [LVarSubst]
composeOrientedUnifs domL domR (subst, substs) = do
  r1 <- toVarSubst subst
  traverse (mergeLVarSubsts r1) $ mapMaybe (couldBeRenaming domL domR) substs

unifyLTermOriented :: IsConst c => (c -> LSort) -> [Equal (LTerm c)] -> WithMaude (Maybe [LVarSubst])
unifyLTermOriented sortOf eqs = composeOrientedUnifs domL domR <$> unifyLTermFactored sortOf eqs
  where
    varsSide :: IsConst c => (Equal (LTerm c) -> LTerm c) -> [Equal (LTerm c)] -> S.Set LVar
    varsSide f = S.fromList . freesList . map f

    domL = varsSide eqLHS eqs
    domR = varsSide eqRHS eqs

unifyLNTermOriented :: [Equal LNTerm] -> WithMaude (Maybe [LVarSubst])
unifyLNTermOriented = unifyLTermOriented sortOfName

-- | @unifyLNTerm eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLNTerm :: [Equal LNTerm] -> WithMaude [LNSubstVFresh]
unifyLNTerm = unifyLTerm sortOfName

unifyLNTerms :: LNTerm -> LNTerm -> WithMaude [LNSubstVFresh]
unifyLNTerms fa1 fa2 = unifyLNTerm [Equal fa1 fa2]

-- | 'True' iff the terms are unifiable.
unifiableLNTerms :: LNTerm -> LNTerm -> WithMaude Bool
unifiableLNTerms t = fmap (not . null) . unifyLNTerms t

eqLNTerms :: LNTerm -> LNTerm -> WithMaude Bool
eqLNTerms t1 t2 = any (isJust . couldBeRenaming (termDom t1) (termDom t2)) <$> unifyLNTerms t1 t2
  where
    termDom :: LNTerm -> S.Set LVar
    termDom = foldFrees S.singleton

-- | Check whether to substitutions are equal modulo renaming. NOTE: Relies on
--   the invariant that the substitutions are disjoint or equal in their values,
--   i.e., a ~> b*c and a ~> c*d will not be recognized as equal, but
--   a ~> b*c and a ~> d*e will.
eqSubsts :: LNSubst -> LNSubst -> WithMaude Bool
eqSubsts (sMap -> s1) (sMap -> s2) = zipMapping (M.toAscList s1) (M.toAscList s2)
  where
    -- This function should be called on the the sorted input maps' keys list.
    -- The keys of the map must exactly match for the substitutions to be
    -- equivalent. That's why we can simply zip them and recursively check
    -- whether the list head matches.
    zipMapping :: [(LVar, LNTerm)] -> [(LVar, LNTerm)] -> WithMaude Bool
    zipMapping [] [] = return True
    zipMapping [] _ = return False
    zipMapping _ [] = return False
    zipMapping ((v, term) : t) ((v', term') : t')
      | v == v' = do
        r <- zipMapping t t'
        eq <- eqLNTerms term term'
        -- Prioritize (by &&-laziness) recursion over term equivalance because
        -- "easy" False's can come from pattern-matching (no need to call maude).
        return (r && eq)
      | otherwise = return False

-- | Flatten a factored substitution to a list of substitutions.
flattenUnif :: IsConst c => (LSubst c, [LSubstVFresh c]) -> [LSubstVFresh c]
flattenUnif (subst, substs) = map (`composeVFresh` subst) substs

-- Unification without AC
----------------------------------------------------------------------

-- | @unifyLTermFactoredAC sortOf eqs@ returns a complete set of unifiers for @eqs@ for terms without AC symbols.
unifyLTermFactoredNoAC :: (IsConst c)
                   => (c -> LSort)
                   -> [Equal (LTerm c)]
                   -> [(SubstVFresh c LVar)]
unifyLTermFactoredNoAC sortOf eqs = do
    solve $ execRWST unif sortOf M.empty
  where
    unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
    solve Nothing         = []
    solve (Just (m, []))  = [freeToFreshRaw (substFromMap m)]
    -- if delayed AC unifications occur, we fail
    solve (Just _     )   = error "No AC unification, but AC symbol found."


-- | @unifyLNTermFactoredNoAC sortOf eqs@ returns a complete set of unifiers for @eqs@ for terms without AC symbols.
unifyLNTermFactoredNoAC :: [Equal LNTerm]
                    -> [(SubstVFresh Name LVar)]
unifyLNTermFactoredNoAC = unifyLTermFactoredNoAC sortOfName

-- | @unifyLNTermNoAC eqs@ returns a complete set of unifiers for @eqs@  for terms without AC symbols.
unifyLTermNoAC :: (IsConst c)
           => (c -> LSort)
           -> [Equal (LTerm c)]
           -> [SubstVFresh c LVar]
unifyLTermNoAC sortOf eqs = unifyLTermFactoredNoAC sortOf eqs

-- | @unifyLNTermNoAC eqs@ returns a complete set of unifiers for @eqs@  for terms without AC symbols.
unifyLNTermNoAC :: [Equal LNTerm] -> [SubstVFresh Name LVar]
unifyLNTermNoAC = unifyLTermNoAC sortOfName

-- | 'True' iff the terms are unifiable.
unifiableLNTermsNoAC :: LNTerm -> LNTerm -> Bool
unifiableLNTermsNoAC t1 t2 = not $ null $ unifyLNTermNoAC [Equal t1 t2]

-- Matching modulo AC
----------------------------------------------------------------------

-- | Match an 'LVar' term to an 'LVar' pattern.
matchLVar :: LVar -> LVar -> Match (LTerm c)
matchLVar t p = varTerm t `matchWith` varTerm p

-- | @solveMatchLNTerm sortOf eqs@ returns a complete set of matchers for
-- @eqs@ modulo AC.
solveMatchLTerm :: (IsConst c)
           => (c -> LSort)
           -> Match (LTerm c)
           -> WithMaude [Subst c LVar]
solveMatchLTerm sortOf matchProblem =
    case flattenMatch matchProblem of
      Nothing -> pure []
      Just ms -> reader $ matchTerms ms
  where
    matchTerms ms hnd =
        case runState (runExceptT match) M.empty of
          (Left NoMatcher, _)  -> []
          (Left ACProblem, _)  ->
              unsafePerformIO (UM.matchViaMaude hnd sortOf matchProblem)
          (Right (), mappings) -> [substFromMap mappings]
      where
        match = forM_ ms $ \(t, p) -> matchRaw sortOf t p


-- | @solveMatchLNTerm eqs@ returns a complete set of matchers for @eqs@
-- modulo AC.
solveMatchLNTerm :: Match LNTerm -> WithMaude [Subst Name LVar]
solveMatchLNTerm = solveMatchLTerm sortOfName

-- Free unification with lazy AC-equation solving.
--------------------------------------------------------------------

type UnifyRaw c = RWST (c -> LSort) [Equal (LTerm c)] (Map LVar (VTerm c LVar)) Maybe

-- | Unify two 'LTerm's with delayed AC-unification.
unifyRaw :: IsConst c => LTerm c -> LTerm c -> UnifyRaw c ()
unifyRaw l0 r0 = do
    sortOf <- ask
    l <- gets ((`applyVTerm` l0) . substFromMap)
    r <- gets ((`applyVTerm` r0) . substFromMap)
    case (viewTerm l, viewTerm r) of
       (Lit (Var vl), Lit (Var vr))
         | vl == vr  -> return ()
         | otherwise -> case (lvarSort vl, lvarSort vr) of
             (sl, sr) | sl == sr                 -> elim vl r
             _        | sortGeqLTerm sortOf vl r -> elim vl r
             -- If unification can succeed here, then it must work by
             -- elimating the right-hand variable with the left-hand side.
             _                                   -> elim vr l

       (Lit (Var vl),  _            ) -> elim vl r
       (_,             Lit (Var vr) ) -> elim vr l
       (Lit (Con cl),  Lit (Con cr) ) -> guard (cl == cr)
       -- Special cases for builtin naturals: Make sure to perform unification
       -- via Maude if we have 1:nat on the left-/right-hand side.
       (FApp (NoEq lfsym) [], FApp (AC NatPlus) _) ->
          guard (lfsym == natOneSym) >> tell [Equal l r]
       (FApp (AC NatPlus) _, FApp (NoEq rfsym) []) ->
          guard (rfsym == natOneSym) >> tell [Equal l r]
       -- General cases / function application
       (FApp (NoEq lfsym) largs, FApp (NoEq rfsym) rargs) ->
           guard (lfsym == rfsym && length largs == length rargs)
           >> sequence_ (zipWith unifyRaw largs rargs)
       (FApp List largs, FApp List rargs) ->
           guard (length largs == length rargs)
           >> sequence_ (zipWith unifyRaw largs rargs)
       -- NOTE: We assume here that terms of the form mult(t) never occur.
       (FApp (AC lacsym) _, FApp (AC racsym) _) ->
           guard (lacsym == racsym) >> tell [Equal l r]  -- delay unification

       (FApp (C lsym) largs, FApp (C rsym) rargs) ->
           guard (lsym == rsym && length largs == length rargs)
           >> tell [Equal l r]  -- delay unification

       -- all unifiable pairs of term constructors have been enumerated
       _                      -> mzero -- no unifier
  where
    elim v t
      | v `occurs` t = mzero -- no unifier
      | otherwise    = do
          sortOf <- ask
          guard  (sortGeqLTerm sortOf v t)
          modify (M.insert v t . M.map (applyVTerm (substFromList [(v,t)])))


data MatchFailure = NoMatcher | ACProblem

instance Semigroup MatchFailure where
  _ <> _ = NoMatcher

instance Monoid MatchFailure where
  mempty = NoMatcher

-- | Ensure that the computed substitution @sigma@ satisfies
-- @t ==_AC apply sigma p@ after the delayed equations are solved.
matchRaw :: IsConst c
         => (c -> LSort)
         -> LTerm c -- ^ Term @t@
         -> LTerm c -- ^ Pattern @p@.
         -> ExceptT MatchFailure (State (Map LVar (VTerm c LVar))) ()
matchRaw sortOf t p = do
    mappings <- get
    case (viewTerm t, viewTerm p) of
      (_, Lit (Var vp)) ->
          case M.lookup vp mappings of
              Nothing             -> do
                unless (sortGeqLTerm sortOf vp t) $
                    throwError NoMatcher
                modify (M.insert vp t)
              Just tp | t == tp  -> return ()
                      | otherwise -> throwError NoMatcher

      (Lit (Con ct),  Lit (Con cp)) -> guard (ct == cp)
      (FApp (NoEq tfsym) targs, FApp (NoEq pfsym) pargs) ->
           guard (tfsym == pfsym && length targs == length pargs)
           >> sequence_ (zipWith (matchRaw sortOf) targs pargs)
      (FApp List targs, FApp List pargs) ->
           guard (length targs == length pargs)
           >> sequence_ (zipWith (matchRaw sortOf) targs pargs)
      (FApp (AC _) _, FApp (AC _) _) -> throwError ACProblem
      (FApp (C _) _, FApp (C _) _) -> throwError ACProblem

      -- all matchable pairs of term constructors have been enumerated
      _                      -> throwError NoMatcher


-- | @sortGreaterEq v t@ returns @True@ if the sort ensures that the sort of @v@ is greater or equal to
--   the sort of @t@.
sortGeqLTerm :: IsConst c => (c -> LSort) -> LVar -> LTerm c -> Bool
sortGeqLTerm st v t = do
    case (lvarSort v, sortOfLTerm st t) of
        (s1, s2) | s1 == s2     -> True
        -- Node is incomparable to all other sorts, invalid input
        (LSortNode,  _        ) -> errNodeSort
        (_,          LSortNode) -> errNodeSort
        (s1, s2)                -> sortCompare s1 s2 `elem` [Just EQ, Just GT]
  where
    errNodeSort = error $
        "sortGeqLTerm: node sort misuse " ++ show v ++ " -> " ++ show t
