module Data.Word32 where

open import Data.Bool
open import Data.Char

{-#
  FOREIGN GHC

  import Data.Bits
  import Data.Word

  data Byte = Byte Bool Bool Bool Bool Bool Bool Bool Bool
  data Bytes = Bytes Byte Byte Byte Byte

  byteToWord8 :: Byte -> Word8
  byteToWord8 (Byte b0 b1 b2 b3 b4 b5 b6 b7) =
    boolToBit b0 0 + boolToBit b1 1 + boolToBit b2 2 + boolToBit b3 3 +
    boolToBit b4 4 + boolToBit b5 5 + boolToBit b6 6 + boolToBit b7 7
    where
      boolToBit b i = if b then bit i else 0

  word8ToByte :: Word8 -> Byte
  word8ToByte w =
    Byte
      (testBit w 0) (testBit w 1) (testBit w 2) (testBit w 3)
      (testBit w 4) (testBit w 5) (testBit w 6) (testBit w 7)

  bytesToWord32 :: Bytes -> Word32
  bytesToWord32 (Bytes b0 b1 b2 b3) =
    byteToWordShifted b0 0 + byteToWordShifted b1 1 + byteToWordShifted b2 2 + byteToWordShifted b3 3
    where
      byteToWordShifted :: Byte -> Int -> Word32
      byteToWordShifted b i = shift (fromIntegral $ byteToWord8 b) (i * 8)

  word32ToBytes :: Word32 -> Bytes
  word32ToBytes w = Bytes (getByte w 0) (getByte w 1) (getByte w 2) (getByte w 3)
    where
      getByte :: Word32 -> Int -> Byte
      getByte w i = word8ToByte $ fromIntegral (shift w (-i * 8))

  bytesToChar :: Bytes -> Char
  bytesToChar = toEnum . fromIntegral . bytesToWord32

  charToBytes :: Char -> Bytes
  charToBytes = word32ToBytes . fromIntegral . fromEnum
#-}

data Byte : Set where
  mkByte : Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Byte

data Word32 : Set where
  mkWord32 : Byte -> Byte -> Byte -> Byte -> Word32

{-# COMPILE GHC Byte = data Byte (Byte) #-}
{-# COMPILE GHC Word32 = data Bytes (Bytes) #-}

postulate
  bytesToChar : Word32 -> Char
  charToBytes : Char -> Word32

{-# COMPILE GHC bytesToChar = bytesToChar #-}
{-# COMPILE GHC charToBytes = charToBytes #-}

word32ToChar : Word32 -> Char
word32ToChar = bytesToChar

charToWord32 : Char -> Word32
charToWord32 = charToBytes
