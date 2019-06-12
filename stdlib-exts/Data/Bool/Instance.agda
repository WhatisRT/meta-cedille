module Data.Bool.Instance where

open import Class.Equality
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

instance
  Bool-Eq : Eq Bool
  Bool-Eq = record { _≟_ = helper }
    where
      helper : ∀ (x y : Bool) → Dec (x ≡ y)
      helper false false = yes refl
      helper false true = no (λ ())
      helper true false = no (λ ())
      helper true true = yes refl
