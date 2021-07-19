module Data.Unit.Instance where

open import Class.Monoid
open import Data.Unit.Polymorphic

instance
  Unit-Monoid : ∀ {a} → Monoid {a} ⊤
  Unit-Monoid = record { mzero = tt ; _+_ = λ _ _ -> tt }
