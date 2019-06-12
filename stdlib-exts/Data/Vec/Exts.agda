module Data.Vec.Exts where

open import Class.Monad
open import Data.Fin
open import Data.Maybe
open import Data.Maybe.Instance
open import Data.Nat
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary
open import Relation.Unary

findIndex : {n : ℕ} {A : Set} {P : A -> Set} -> Decidable P -> Vec A n -> Maybe (Fin n)
findIndex P? [] = nothing
findIndex P? (x ∷ v) with P? x
... | yes p = just zero
... | no ¬p = mmap suc (findIndex P? v)
