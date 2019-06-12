module Data.SimpleMap where

open import Class.Equality
open import Class.Map
open import Data.Maybe
open import Data.List hiding (lookup)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation

SimpleMap : Set -> Set -> Set
SimpleMap A B = List (A × B)

private

  simpleRemove : ∀ {A B} {{_ : Eq A}} -> A -> SimpleMap A B -> SimpleMap A B
  simpleRemove k m = filter (λ {(k' , _) → ¬? (k ≟ k')}) m

  simpleInsert : ∀ {A B} {{_ : Eq A}} -> A -> B -> SimpleMap A B -> SimpleMap A B
  simpleInsert k v m = (k , v) ∷ (simpleRemove k m)

  simpleLookup : ∀ {A B} {{_ : Eq A}} -> A -> SimpleMap A B -> Maybe B
  simpleLookup k [] = nothing
  simpleLookup k ((fst , snd) ∷ m) with k ≟ fst
  simpleLookup k ((fst , snd) ∷ m) | yes p = just snd
  simpleLookup k ((fst , snd) ∷ m) | no ¬p = simpleLookup k m

  simpleMapSnd : ∀ {A B C} -> (B -> C) -> SimpleMap A B -> SimpleMap A C
  simpleMapSnd f [] = []
  simpleMapSnd f ((fst , snd) ∷ m) = (fst , f snd) ∷ (simpleMapSnd f m)

instance
  MapClass-Simple : MapClass SimpleMap
  MapClass-Simple = record
    { insert = simpleInsert
    ; remove = simpleRemove
    ; lookup = simpleLookup
    ; mapSnd = simpleMapSnd
    ; emptyMap = [] }
