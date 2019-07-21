module Data.Word64.Exts where

open import Agda.Builtin.Nat
open import Agda.Builtin.Word
open import Data.Nat
open import Data.Word

addWord : Word64 → Word64 → Word64
addWord a b = primWord64FromNat (primWord64ToNat a + primWord64ToNat b)

subWord : Word64 → Word64 → Word64
subWord a b = primWord64FromNat ((primWord64ToNat a + 18446744073709551616) - primWord64ToNat b)
