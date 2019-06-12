module Data.Unit.Instance where

open import Class.Monoid
open import Data.Unit

instance
  Unit-Monoid : Monoid ⊤
  Unit-Monoid = record { mzero = tt ; _+_ = λ _ _ -> tt }
