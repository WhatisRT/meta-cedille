module Data.Nat.Instance where

open import Class.Equality
open import Class.Monoid
open import Class.Show
open import Data.Char
open import Data.List
open import Data.Nat renaming (_≟_ to _≟ℕ_; _+_ to _+ℕ_)
open import Data.String
open import Function

private

  postulate
    primShowNat : ℕ -> List Char

  {-# COMPILE GHC primShowNat = show #-}

  showNat : ℕ -> String
  showNat = fromList ∘ primShowNat

instance
  Eq-ℕ : Eq ℕ
  Eq-ℕ = record { _≟_ = _≟ℕ_ }

  ℕ-Monoid : Monoid ℕ
  ℕ-Monoid = record { mzero = zero ; _+_ = _+ℕ_ }

  Show-ℕ : Show ℕ
  Show-ℕ = record { show = showNat }
