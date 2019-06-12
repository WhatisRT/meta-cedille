module Data.Fin.Map where

open import Class.Monad
open import Data.Nat
open import Data.Fin
open import Function

DepFinMap : ∀ {a} (n : ℕ) (A : Fin n -> Set a) -> Set a
DepFinMap n A = (k : Fin n) -> A k

FinMap : ∀ {a} (n : ℕ) -> Set a -> Set a
FinMap n A = DepFinMap n (λ _ -> A)

sequenceDepFinMap : ∀ {a n A} {M : Set a -> Set a} {{_ : Monad M}}
  -> DepFinMap n (λ x -> M $ A x) -> M (DepFinMap n A)
sequenceDepFinMap {n = zero} f = return λ ()
sequenceDepFinMap {n = suc n} f = do
  f' <- sequenceDepFinMap $ f ∘ suc
  fzero <- f zero
  return λ
    { zero → fzero
    ; (suc v) → f' v}
