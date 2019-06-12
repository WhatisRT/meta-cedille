module Class.Equality where

open import Data.Bool using (Bool; if_then_else_)
open import Data.List
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

record Eq (A : Set) : Set where
  field
    _≟_ : (x y : A) -> Dec (x ≡ y)

open Eq {{...}} public

_≣_ : ∀ {A} {{_ : Eq A}} -> A -> A -> Bool
x ≣ y = ⌊ x ≟ y ⌋

decCase_of_default_ : ∀ {a} {A : Set} {B : Set a} {{_ : Eq A}} -> A -> List (A × B) -> B -> B
decCase a of [] default d = d
decCase a of x ∷ xs default d = if a ≣ proj₁ x then proj₂ x else (decCase a of xs default d)
