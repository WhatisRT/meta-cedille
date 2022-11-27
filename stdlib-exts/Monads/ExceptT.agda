module Monads.ExceptT where

open import Class.Monad
open import Class.Monad.Except
open import Class.Monad.Reader
open import Class.Monad.State
open import Class.MonadTrans
open import Data.Sum
open import Function
open import Level

private
  variable
    a : Level

ExceptT : (M : Set a -> Set a) -> Set a -> Set a -> Set a
ExceptT M E A = M (E ⊎ A)

ExceptT-MonadTrans : {E : Set a} -> MonadTrans (λ (M : Set a -> Set a) -> ExceptT M E)
ExceptT-MonadTrans .embed x = x >>= return ∘ inj₂

module _ {M : Set a -> Set a} {{_ : Monad M}} {E : Set a} where

  runExceptT : ∀ {A} → ExceptT M E A → M (E ⊎ A)
  runExceptT x = x

  ExceptT-Monad : Monad (ExceptT M E)
  ExceptT-Monad ._>>=_ x f = x >>= λ { (inj₁ y) -> return $ inj₁ y ; (inj₂ y) -> f y }
  ExceptT-Monad .return x  = return $ inj₂ x

  ExceptT-MonadExcept : MonadExcept (ExceptT M E) {{ExceptT-Monad}} E
  ExceptT-MonadExcept .throwError = return ∘ inj₁
  ExceptT-MonadExcept .catchError x f = x >>= λ { (inj₁ x) → f x ; (inj₂ y) → return {{ExceptT-Monad}} y }

  ExceptT-MonadState : ∀ {S} {{_ : MonadState M S}} -> MonadState (ExceptT M E) {{ExceptT-Monad}} S
  ExceptT-MonadState .get = embed {{ExceptT-MonadTrans}} get
  ExceptT-MonadState .put = embed {{ExceptT-MonadTrans}} ∘ put

  ExceptT-MonadReader : ∀ {R} {{_ : MonadReader M R}} -> MonadReader (ExceptT M E) R ⦃ ExceptT-Monad ⦄
  ExceptT-MonadReader .ask   = embed ⦃ ExceptT-MonadTrans ⦄ ask
  ExceptT-MonadReader .local = local
