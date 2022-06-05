module Class.Traversable where

open import Class.Functor
open import Class.Monad
open import Level

record Traversable {a} (T : Set a -> Set a) : Set (suc a) where
  field
    sequence : ∀ {M : Set a -> Set a} {{_ : Monad M}} {A : Set a} -> T (M A) -> M (T A)

  traverse : ∀ {M : Set a -> Set a} ⦃ _ : Monad M ⦄ ⦃ _ : Functor T ⦄ {A B : Set a} → (A → M B) → T A → M (T B)
  traverse ⦃ _ ⦄ ⦃ fun-T ⦄ f x = sequence (_<$>_ ⦃ fun-T ⦄ f x)

open Traversable {{...}} public
