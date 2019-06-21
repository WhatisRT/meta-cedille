module Data.Product.Instance where

open import Class.Equality
open import Class.Monoid
open import Class.Show
open import Data.Product
open import Data.String.Instance
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

instance
  Product-Eq : ∀ {A B} {{_ : Eq A}} {{_ : Eq B}} -> Eq (A × B)
  Product-Eq {A} {B} = record { _≟_ = helper }
    where
      helper : (x x' : A × B) -> Dec (x ≡ x')
      helper (fst , snd) (fst₁ , snd₁) with fst ≟ fst₁ | snd ≟ snd₁
      ... | yes p | yes p₁ rewrite p | p₁ = yes refl
      ... | yes p | no ¬p = no λ { refl -> ¬p refl }
      ... | no ¬p | H' = no λ { refl -> ¬p refl }

  Product-Monoid : ∀ {a} {A B : Set a} -> {{_ : Monoid A}} -> {{_ : Monoid B}} -> Monoid (A × B)
  Product-Monoid = record
    { mzero = mzero , mzero
    ; _+_ = λ { (x1 , x2) (y1 , y2) -> (x1 + y1) , (x2 + y2) } }

  Product-Show : ∀ {a} {A B : Set a} {{_ : Show A}} {{_ : Show B}} -> Show (A × B)
  Product-Show = record { show = λ { (a , b) -> "(" + show a + ", " + show b + ")" } }
