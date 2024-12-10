-- Ignore incomplete pattern matches in this module
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Theory.Proof.CyclicTest
  ( b0
  , b00
  , b01
  , b000
  , b001
  , b0000
  , b0001
  , t0_b01_b0
  , t0_b001_b00
  , t0_b0000_b00
  , t0_b0001_b000
  , t1_b01_b0
  , t1_b000_b00
  , t1_b001_b0
  , t2_b01_b0
  , t2_b000_b00
  , t2_b001_b0
  , testTree0
  , testTree1
  , testTree2
  , foldProof ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Theory.Constraint.System.ID (SystemID, subCaseIDs, rootID)
import Theory.Proof (LTree (LNode))
import Theory.Proof.Cyclic (CyclicProof, toProof, BackLink (BackLink), ProgressingVars (PVs), updateFinished)
import Term.LTerm (NodeId, LVar (LVar), LSort (LSortNode))
import Data.Maybe (fromMaybe)
import Theory.Constraint.Renaming (idRenaming)

t :: NodeId
t = LVar "t" LSortNode 0

vk :: NodeId
vk = LVar "vk" LSortNode 0

vk1 :: NodeId
vk1 = LVar "vk" LSortNode 1

vk2 :: NodeId
vk2 = LVar "vk" LSortNode 2

vk3 :: NodeId
vk3 = LVar "vk" LSortNode 2

vr :: NodeId
vr = LVar "vr" LSortNode 0

vr1 :: NodeId
vr1 = LVar "vr" LSortNode 1

b0 :: SystemID
b0 = rootID

b00 :: SystemID
b01 :: SystemID
[ b00, b01 ] = map ($ b0) (subCaseIDs 2)

b000 :: SystemID
b001 :: SystemID
[ b000, b001 ] = map ($ b00) (subCaseIDs 2)

b0000 :: SystemID
b0001 :: SystemID
[ b0000, b0001 ] = map ($ b000) (subCaseIDs 2)

t0_b01_b0 :: CyclicProof
t0_b001_b00 :: CyclicProof
t0_b0000_b00 :: CyclicProof
t0_b0001_b000 :: CyclicProof
[ t0_b01_b0, t0_b001_b00, t0_b0000_b00, t0_b0001_b000 ] = map toProof
  [ BackLink (b01, b0) idRenaming (PVs (S.fromList [t, vk, vk1]) (S.fromList [t, vk, vk1]))
  , BackLink (b001, b00) idRenaming (PVs (S.fromList [vr, vk1, vk2]) (S.fromList [vr, vk1, vk2, t]))
  , BackLink (b0000, b00) idRenaming (PVs (S.fromList [vr, vk1, vk2]) (S.fromList [vr, vk1, vk2, t]))
  , BackLink (b0001, b000) idRenaming (PVs (S.fromList [vr1]) (S.fromList [vr1, t, vr, vk1, vr1, vk2, vk3])) ]

testTree0 :: LTree SystemID (SystemID, Maybe CyclicProof)
testTree0 = LNode (b0, Nothing) $ M.fromList
    [ (b00, LNode (b00, Nothing) $ M.fromList
        [ (b000, LNode (b000, Nothing) $ M.fromList
            [ (b0000, LNode (b0000, Just t0_b0000_b00) M.empty)
            , (b0001, LNode (b0001, Just t0_b0001_b000) M.empty) ])
        , (b001, LNode (b001, Just t0_b001_b00) M.empty) ])
    , (b01, LNode (b01, Just t0_b01_b0) M.empty) ]

t1_b01_b0 :: CyclicProof
t1_b000_b00 :: CyclicProof
t1_b001_b0 :: CyclicProof
[ t1_b01_b0 ,t1_b000_b00 ,t1_b001_b0 ] = map toProof
  [ BackLink (b01, b0) idRenaming (PVs (S.singleton t) (S.singleton t))
  , BackLink (b000, b00) idRenaming (PVs (S.fromList [t, vr]) (S.fromList [t, vr]))
  , BackLink (b001, b0) idRenaming (PVs (S.singleton t) (S.singleton t)) ]

testTree1 :: LTree SystemID (SystemID, Maybe CyclicProof)
testTree1 = LNode (b0, Nothing) $ M.fromList
    [ (b00, LNode (b00, Nothing) $ M.fromList
        [ (b000, LNode (b000, Just t1_b000_b00) M.empty)
        , (b001, LNode (b001, Just t1_b001_b0) M.empty)])
    , (b01, LNode (b01, Just t1_b01_b0) M.empty) ]

t2_b01_b0 :: CyclicProof
t2_b000_b00 :: CyclicProof
t2_b001_b0 :: CyclicProof
[ t2_b01_b0 ,t2_b000_b00 ,t2_b001_b0 ] = map toProof
  [ BackLink (b01, b0) idRenaming (PVs (S.singleton t) (S.singleton t))
  , BackLink (b000, b00) idRenaming (PVs (S.fromList [vr]) (S.fromList [t, vr]))
  , BackLink (b001, b0) idRenaming (PVs (S.singleton t) (S.singleton t)) ]

testTree2 :: LTree SystemID (SystemID, Maybe CyclicProof)
testTree2 = LNode (b0, Nothing) $ M.fromList
    [ (b00, LNode (b00, Nothing) $ M.fromList
        [ (b000, LNode (b000, Just t2_b000_b00) M.empty)
        , (b001, LNode (b001, Just t2_b001_b0) M.empty)])
    , (b01, LNode (b01, Just t2_b01_b0) M.empty) ]

foldProof :: LTree SystemID (SystemID, Maybe CyclicProof) -> CyclicProof
foldProof (LNode (sId, mprf) m)
  | M.null m = fromMaybe (error "invariant error") mprf
  | otherwise = updateFinished sId $ foldr1 (<>) (map foldProof (M.elems m))
