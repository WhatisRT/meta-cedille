module Data.Sum.Instance where

open import Class.Equality
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

instance
  Sum-Eq : {A B : Set} -> {{_ : Eq A}} -> {{_ : Eq B}} -> Eq (A ⊎ B)
  Sum-Eq = record { _≟_ = helper }
    where
      helper : {A B : Set} {{_ : Eq A}} {{_ : Eq B}} -> (x y : A ⊎ B) → Dec (x ≡ y)
      helper (inj₁ x) (inj₁ x₁) with x ≟ x₁
      ... | yes refl = yes refl
      ... | no ¬p = no λ { refl -> ¬p refl }
      helper (inj₁ x) (inj₂ y) = no (λ ())
      helper (inj₂ y₁) (inj₁ x) = no (λ ())
      helper (inj₂ y₁) (inj₂ y) with y ≟ y₁
      ... | yes refl = yes refl
      ... | no ¬p = no λ { refl -> ¬p refl }
