module Data.Vec.Exts where

open import Data.Fin
open import Data.Maybe
open import Data.Nat
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary
open import Relation.Unary
open import Data.Vec.Relation.Unary.Any

findIndex : {n : ℕ} {A : Set} {P : A -> Set} -> Decidable P -> Vec A n -> Maybe (Fin n)
findIndex P? xs with any? P? xs
... | yes ix = just (index ix)
... | no _ = nothing
