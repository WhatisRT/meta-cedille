module Prelude.Nat where

open import Data.Nat
import Data.Fin.Literals as F
import Data.Nat.Literals as ℕ
open import Data.Unit
open import Agda.Builtin.FromNat public

mkNumberInstance : ∀ {A : Set} → (ℕ → A) → Number A
mkNumberInstance fromNat .Number.Constraint _ = ⊤
mkNumberInstance fromNat .fromNat n = fromNat n

instance
  Number-ℕ = ℕ.number

  unitInstance = tt
