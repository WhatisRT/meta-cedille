module Data.Empty.Instance where

open import Class.Equality
open import Class.Show
open import Data.Empty

instance
  Empty-Eq : Eq ⊥
  Empty-Eq = record { _≟_ = λ x () }

  Empty-Show : Show ⊥
  Empty-Show = record { show = λ () }
