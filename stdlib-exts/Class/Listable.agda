module Class.Listable where

open import Class.Equality

open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Fin renaming (_≟_ to _≟F_)
open import Data.Fin.Properties using (suc-injective)

index-injective : ∀ {ℓ} {A : Set ℓ} {a b} {l : List A} → (a∈l : a ∈ l) → (b∈l : b ∈ l) → index a∈l ≡ index b∈l → a ≡ b
index-injective (here refl) (here refl) eq = refl
index-injective (there a∈l) (there b∈l) eq = index-injective a∈l b∈l (suc-injective eq)

record Listable (A : Set) : Set where
  field
    listing  : List A
    complete : (a : A) → a ∈ listing

  Listable→Eq : Eq A
  Listable→Eq ._≟_ = helper complete
    where
      helper : ∀ {A : Set} {l : List A} → ((a : A) → a ∈ l) → (a b : A) → Dec (a ≡ b)
      helper {A} {l} complete a b with complete a | inspect complete a | complete b | inspect complete b
      ... | a∈l | [ eq ] | b∈l | [ eq' ] with index a∈l ≟F index b∈l
      ... | no ¬p = no (λ where refl → ¬p (cong index (trans (sym eq) eq')))
      ... | yes p = yes (index-injective a∈l b∈l p)
