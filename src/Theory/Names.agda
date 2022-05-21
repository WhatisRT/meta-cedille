module Theory.Names where

import Agda.Builtin.Nat using (_+_; _-_; _==_)

import Data.Product

open import Data.Word using (Word64; toℕ; fromℕ)
open import Data.Word64.Exts

open import Prelude
open import Prelude.Nat

GlobalName : Set
GlobalName = String

𝕀 : Set
𝕀 = Word64

instance
  𝕀-Number : Number 𝕀
  𝕀-Number = mkNumberInstance fromℕ

  𝕀-Eq : Eq 𝕀
  𝕀-Eq = record { _≟_ = Data.Word._≟_ }

  𝕀-EqB : EqB 𝕀
  𝕀-EqB = record { _≣_ = Agda.Builtin.Nat._==_ on toℕ }

  𝕀-Show : Show 𝕀
  𝕀-Show = record { show = show ∘ toℕ }

_<𝕀_ : 𝕀 → 𝕀 → Bool
x <𝕀 y = toℕ x <ᵇ toℕ y

_+𝕀_ : 𝕀 → 𝕀 → 𝕀
_+𝕀_ = addWord

_-𝕀_ : 𝕀 → 𝕀 → 𝕀
_-𝕀_ = subWord

suc𝕀 : 𝕀 → 𝕀
suc𝕀 = _+𝕀 1

pred𝕀 : 𝕀 → 𝕀
pred𝕀 = _-𝕀 1

data Name : Set where
  Bound : 𝕀 → Name
  Free : GlobalName → Name

instance
  Name-Eq : Eq Name
  Name-Eq = record { _≟_ = helper }
    where
      helper : (n n' : Name) → Dec (n ≡ n')
      helper (Bound x) (Bound x₁) with x ≟ x₁
      ... | yes p rewrite p = yes refl
      ... | no ¬p = no λ { refl → ¬p refl }
      helper (Bound x) (Free x₁) = no λ ()
      helper (Free x) (Bound x₁) = no λ ()
      helper (Free x) (Free x₁) with x ≟ x₁
      ... | yes p rewrite p = yes refl
      ... | no ¬p = no λ { refl → ¬p refl }

  Name-EqB : EqB Name
  Name-EqB = Eq→EqB

  Name-Show : Show Name
  Name-Show = record { show = helper }
    where
      helper : Name → String
      helper (Bound x) = show x
      helper (Free x) = x

showVar : List String → Name → String
showVar l (Bound x) with lookupMaybe (toℕ x) l
... | nothing = show x
... | just x₁ = if x₁ ≣ "_" then show x else x₁
showVar l (Free x) = x
