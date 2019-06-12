module Monads.ExceptT where

open import Class.Monad
open import Class.Monad.Except
open import Class.Monad.State
open import Class.MonadTrans
open import Data.Sum
open import Function

ExceptT : ∀ {a b} (M : Set a -> Set b) -> Set a -> Set a -> Set b
ExceptT M E A = M (E ⊎ A)

ExceptT-MonadTrans : ∀ {a b} {E : Set a} -> MonadTrans {a} (λ (M : Set a -> Set b) -> ExceptT M E)
ExceptT-MonadTrans = record { embed = λ x -> x >>= (return ∘ inj₂) ; transform = λ τ x -> τ _ x }

module ExceptT-Internal {a b} {M : Set a -> Set b} {{mon : Monad M}} {E : Set a} where

  ExceptT-Monad : Monad (ExceptT M E)
  ExceptT-Monad = record { _>>=_ = helper ; return = λ x → (return $ inj₂ x) }
    where
      helper : ∀ {A B} -> ExceptT M E A -> (A -> ExceptT M E B) -> ExceptT M E B
      helper x f = x >>= λ { (inj₁ y) -> return $ inj₁ y ; (inj₂ y) -> f y }

  private
    throwError' : ∀ {A : Set a} -> E -> ExceptT M E A
    throwError' = return ∘ inj₁

    catchError' : ∀ {A : Set a} -> ExceptT M E A -> (E -> ExceptT M E A) -> ExceptT M E A
    catchError' x f = x >>= λ { (inj₁ x) → f x ; (inj₂ y) → return {{ExceptT-Monad}} y }

  ExceptT-MonadExcept : MonadExcept (ExceptT M E) {{ExceptT-Monad}} E
  ExceptT-MonadExcept = record { throwError = throwError' ; catchError = catchError' }

  ExceptT-MonadState : ∀ {S} {{_ : MonadState M S}} -> MonadState (ExceptT M E) {{ExceptT-Monad}} S
  ExceptT-MonadState = record
    { get = embed {{ExceptT-MonadTrans}} get
    ; put = embed {{ExceptT-MonadTrans}} ∘ put
    ; state = embed {{ExceptT-MonadTrans}} ∘ state }

open ExceptT-Internal public
