module Data.List.Exts where

open import Class.Equality
open import Class.Monad
open import Class.Functor
open import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Instance
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Relation.Nullary
open import Relation.Unary

lookupMaybe : ∀ {a} {A : Set a} -> ℕ -> List A -> Maybe A
lookupMaybe n [] = nothing
lookupMaybe zero (x ∷ l) = just x
lookupMaybe (suc n) (x ∷ l) = lookupMaybe n l

findIndexList : {A : Set} {P : A -> Set} -> Decidable P -> List A -> Maybe ℕ
findIndexList P? [] = nothing
findIndexList P? (x ∷ v) with P? x
... | yes p = just 0
... | no ¬p = suc <$> findIndexList P? v

dropHeadIfAny : ∀ {a} {A : Set a} -> List A -> List A
dropHeadIfAny [] = []
dropHeadIfAny (x ∷ l) = l

{-# TERMINATING #-}
splitMulti : ∀ {A : Set} {{_ : Eq A}} -> A -> List A -> List (List A)
splitMulti a [] = []
splitMulti a l@(x ∷ xs) with break (a ≟_) l
... | fst , snd = fst ∷ splitMulti a (dropHeadIfAny snd)

takeEven : ∀ {a} {A : Set a} -> List A -> List A
takeEven [] = []
takeEven (x ∷ []) = []
takeEven (x ∷ x₁ ∷ l) = x₁ ∷ takeEven l
