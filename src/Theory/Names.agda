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
  𝕀-EqB = record { _≣_ = wordEq }

  𝕀-Show : Show 𝕀
  𝕀-Show = record { show = show ∘ toℕ }

_<𝕀_ : 𝕀 → 𝕀 → Bool
x <𝕀 y = toℕ x <ᵇ toℕ y

_+𝕀_ : 𝕀 → 𝕀 → 𝕀
_+𝕀_ = addWord

_-𝕀_ : 𝕀 → 𝕀 → 𝕀
_-𝕀_ = subWord

_⊔𝕀_ : 𝕀 → 𝕀 → 𝕀
_⊔𝕀_ = wordMax

suc𝕀 : 𝕀 → 𝕀
suc𝕀 = _+𝕀 1

pred𝕀 : 𝕀 → 𝕀
pred𝕀 = _-𝕀 1

data Name : Set where
  Bound : 𝕀 → Name
  Free : GlobalName → Name

instance
  Name-Eq : Eq Name
  Name-Eq ._≟_ (Bound x) (Bound x₁) with x ≟ x₁
  ... | yes p rewrite p = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  Name-Eq ._≟_ (Bound x) (Free x₁) = no λ ()
  Name-Eq ._≟_ (Free x) (Bound x₁) = no λ ()
  Name-Eq ._≟_ (Free x) (Free x₁) with x ≟ x₁
  ... | yes p rewrite p = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }

  Name-EqB : EqB Name
  Name-EqB ._≣_ (Bound x) (Bound x₁) = x ≣ x₁
  Name-EqB ._≣_ (Bound x) (Free x₁) = false
  Name-EqB ._≣_ (Free x) (Bound x₁) = false
  Name-EqB ._≣_ (Free x) (Free x₁) = x ≣ x₁

  Name-Show : Show Name
  Name-Show .show (Bound x) = show x
  Name-Show .show (Free x) = x

showVar : List String → Name → String
showVar l (Bound x) with lookupMaybe (toℕ x) l
... | nothing = "DB" + show x
... | just x₁ = if x₁ ≣ "_" ∨ x₁ ≣ "" then show x else x₁
showVar l (Free x) = x
