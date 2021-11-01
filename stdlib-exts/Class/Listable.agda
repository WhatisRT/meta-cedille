module Class.Listable where

open import Class.Equality

open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

record Listable (A : Set) : Set where
  field
    listing  : List A
    unique   : Unique listing
    complete : (a : A) → a ∈ listing

  Listable→Eq : Eq A
  Listable→Eq ._≟_ a b = helper (complete a) (complete b) unique
    where
      helper : ∀ {a b} {l : List A} → (a ∈ l) → (b ∈ l) → Unique l → Dec (a ≡ b)
      helper {a} {b} {l} h h' u with l | h | h' | u
      ... | ._ | here refl | here refl | _      = yes refl
      ... | ._ | here refl | there h   | h' ∷ _ = no λ where refl → All¬⇒¬Any h' h
      ... | ._ | there h   | here refl | h' ∷ _ = no λ where refl → All¬⇒¬Any h' h
      ... | ._ | there h   | there h'  | _  ∷ u = helper h h' u
