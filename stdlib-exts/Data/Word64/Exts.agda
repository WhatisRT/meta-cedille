module Data.Word64.Exts where

open import Agda.Builtin.Nat
open import Agda.Builtin.Word
open import Data.Bool
open import Data.Nat
open import Data.Word

addWord : Word64 → Word64 → Word64
addWord a b = primWord64FromNat (primWord64ToNat a + primWord64ToNat b)
{-# COMPILE GHC addWord = (+) #-}

subWord : Word64 → Word64 → Word64
subWord a b = primWord64FromNat (primWord64ToNat a - primWord64ToNat b)
{-# COMPILE GHC subWord = \ a b -> if a > b then a - b else 0 #-}

postulate
  wordEq : Word64 → Word64 → Bool
  wordMax : Word64 → Word64 → Word64
{-# COMPILE GHC wordEq = (==) #-}
{-# COMPILE GHC wordMax = max #-}
