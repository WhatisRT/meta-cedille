module Data.List.Exts where

open import Class.Equality
open import Class.Monad
open import Class.Functor
open import Data.Bool hiding (_≟_)
open import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Instance
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Product
open import Relation.Nullary
open import Relation.Unary

private
  variable
    A : Set

lookupMaybe : ∀ {a} {A : Set a} -> ℕ -> List A -> Maybe A
lookupMaybe n [] = nothing
lookupMaybe zero (x ∷ l) = just x
lookupMaybe (suc n) (x ∷ l) = lookupMaybe n l

findIndexList : {A : Set} -> (A → Bool) -> List A -> Maybe ℕ
findIndexList P? [] = nothing
findIndexList P? (x ∷ v) with P? x
... | true  = just 0
... | false = suc <$> findIndexList P? v

dropHeadIfAny : ∀ {a} {A : Set a} -> List A -> List A
dropHeadIfAny [] = []
dropHeadIfAny (x ∷ l) = l

-- inverse to intercalate
{-# TERMINATING #-}
splitMulti : ∀ {A : Set} {{_ : Eq A}} -> A -> List A -> List (List A)
splitMulti a [] = []
splitMulti a l@(x ∷ xs) with break (a ≟_) l
... | fst , snd = fst ∷ splitMulti a (dropHeadIfAny snd)

takeEven : ∀ {a} {A : Set a} -> List A -> List A
takeEven [] = []
takeEven (x ∷ []) = []
takeEven (x ∷ x₁ ∷ l) = x₁ ∷ takeEven l

maximum : List ℕ → ℕ
maximum [] = 0
maximum (x ∷ l) = x ⊔ maximum l

mapWithIndex : ∀ {a b} {A : Set a} {B : Set b} → (ℕ → A → B) → List A → List B
mapWithIndex {A = A} {B} f = helper 0
  where
    helper : ℕ → List A → List B
    helper i []      = []
    helper i (x ∷ l) = f i x ∷ helper (suc i) l

isInit : ⦃ EqB A ⦄ → List A → List A → Bool
isInit [] l' = true
isInit (x ∷ l) [] = false
isInit (x ∷ l) (x₁ ∷ l') = x ≣ x₁ ∧ isInit l l'
