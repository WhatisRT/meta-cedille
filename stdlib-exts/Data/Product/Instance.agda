module Data.Product.Instance where

open import Class.Equality
open import Class.Monoid
open import Class.Show
open import Data.Product
open import Data.Product.Properties
open import Data.String.Instance
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

instance
  Product-Eq : ∀ {A B} {{_ : Eq A}} {{_ : Eq B}} -> Eq (A × B)
  Product-Eq {A} {B} = record { _≟_ = ≡-dec _≟_ _≟_ }

  Product-Monoid : ∀ {a} {A B : Set a} -> {{_ : Monoid A}} -> {{_ : Monoid B}} -> Monoid (A × B)
  Product-Monoid = record
    { mzero = mzero , mzero
    ; _+_ = λ { (x1 , x2) (y1 , y2) -> (x1 + y1) , (x2 + y2) } }

  Product-Show : ∀ {a} {A B : Set a} {{_ : Show A}} {{_ : Show B}} -> Show (A × B)
  Product-Show = record { show = λ { (a , b) -> "(" + show a + ", " + show b + ")" } }
