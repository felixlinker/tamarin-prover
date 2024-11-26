{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Theory.Constraint.System.ID
  ( SystemID
  , rootID
  , subCaseIDs
  , checkRelation
  , maxID ) where

import           Control.DeepSeq (NFData)
import           Data.Binary (Binary)
import qualified Data.Word as W
import qualified Data.Bits as B
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString as SBS
import qualified Data.ByteString.Builder as BSB
import           GHC.Generics (Generic)
import           Utils.PartialOrd (PartialOrdering(..))
import           Data.Maybe (fromMaybe)
import           Control.Basics (guard)

data SystemID = SystemID Int W.Word8 Int BS.ByteString
  deriving( Eq, Ord, Generic, NFData, Binary )

instance Show SystemID where
  show (SystemID off acc _ bs) =
    let bw = B.finiteBitSize acc  -- bit-width
        hbs = SBS.toStrict $ if off /= 0 then BS.cons acc bs else bs
    in      show (SBS.length hbs * bw - ((bw - off) `mod` bw))
        ++  "-"
        ++  BC.unpack (SBS.toStrict (BSB.toLazyByteString (BSB.byteStringHex hbs)))

rootID :: SystemID
rootID = SystemID 1 B.zeroBits 0 BS.empty

subCaseIDs :: Int -> [SystemID -> SystemID]
subCaseIDs n
  | n < 1 = error "cannot count to smaller than 1"
  | otherwise =
    let width = 1 `max` ceiling (logBase 2 (fromIntegral n) :: Float) :: Int
    in  map (inc width) [0..n - 1]
    where
      inc :: Int -> Int -> SystemID -> SystemID
      inc width i s@(SystemID off acc bsl bs)
        | width <= 0  = s
        | otherwise   =
          let accSize = B.finiteBitSize acc
              head' = acc B..|. fromIntegral (B.shiftL i off)
              savedBits = (accSize - off) `min` width
              sid' = if accSize <= savedBits + off
                then SystemID 0 B.zeroBits (succ bsl) (BS.cons head' bs)
                else SystemID (off + savedBits) head' bsl bs
          in inc (width - savedBits) (B.shiftR i savedBits) sid'

checkRelation :: SystemID -> SystemID -> PartialOrdering
checkRelation i1@(SystemID off1 acc1 bsl1 bs1) i2@(SystemID off2 acc2 bsl2 bs2)
  | bsl1 < bsl2 || (bsl1 == bsl2 && off1 < off2) = if checkIsParent i1 i2 then PGT else PINCOMP
  | bsl2 < bsl1 || (bsl1 == bsl2 && off2 < off1) = if checkIsParent i2 i1 then PLT else PINCOMP
  | otherwise = if acc1 == acc2 && bs1 == bs2 then PEQ else PINCOMP
  where
    eight :: Int
    eight = B.finiteBitSize (B.zeroBits :: W.Word8)

    checkIsParent :: SystemID -> SystemID -> Bool
    checkIsParent (SystemID offP accP bslP bsP) (SystemID _ accC bslC bsC) = fromMaybe False $ do
      (acc', t) <- BS.uncons $ BS.drop (fromIntegral $ bslC - bslP) (BS.cons accC bsC)
      let mask = B.shiftR (B.complement B.zeroBits) (eight - offP) :: W.Word8
      guard ((acc' B..&. mask) == accP)
      return $ bsP == t

maxID :: SystemID -> SystemID -> Maybe SystemID
maxID id1 id2 = case checkRelation id1 id2 of
  PGT -> Just id1
  PLT -> Just id2
  PEQ -> Just id1
  PINCOMP -> Nothing
