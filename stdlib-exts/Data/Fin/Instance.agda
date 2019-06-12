module Data.Fin.Instance where

open import Class.Equality
open import Class.Traversable
open import Data.Fin renaming (_≟_ to _≟F_)
open import Data.Fin.Map

instance
  Eq-Fin : ∀ {n} -> Eq (Fin n)
  Eq-Fin = record { _≟_ = _≟F_ }

  Traversable-Fin-Map : ∀ {a} {n} -> Traversable {a} (FinMap n)
  Traversable-Fin-Map = record { sequence = sequenceDepFinMap }
