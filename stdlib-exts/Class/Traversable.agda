module Class.Traversable where

open import Class.Monad
open import Level

record Traversable {a} (T : Set a -> Set a) : Set (suc a) where
  field
    sequence : ∀ {M : Set a -> Set a} {{_ : Monad M}} {A : Set a} -> T (M A) -> M (T A)

open Traversable {{...}} public
