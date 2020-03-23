module Data.Sum.Instance where

open import Class.Equality
open import Class.Monoid
open import Class.Show
open import Data.Bool using (false)
open import Data.String.Instance
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

  Sum-Show : {A B : Set} -> {{_ : Show A}} -> {{_ : Show B}} -> Show (A ⊎ B)
  Sum-Show = record { show = λ { (inj₁ x) → "inj₁ " + show x ; (inj₂ y) → "inj₂ " + show y } }

  Sum-EqB : {A B : Set} -> {{_ : EqB A}} -> {{_ : EqB B}} -> EqB (A ⊎ B)
  Sum-EqB = record { _≣_ = λ { (inj₁ x) (inj₁ y) → x ≣ y
                             ; (inj₁ x) (inj₂ y) → false
                             ; (inj₂ x) (inj₁ y) → false
                             ; (inj₂ x) (inj₂ y) → x ≣ y } }
