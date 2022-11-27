module Class.Monad.Reader where

open import Class.Monad
open import Function
open import Level

private
  variable
    a : Level
    A : Set a

record MonadReader (M : Set a → Set a) (R : Set a) ⦃ _ : Monad M ⦄ : Set (suc a) where
  field
    ask : M R
    local : (R → R) → M A → M A

  reader : (R → A) → M A
  reader f = ask >>= return ∘ f

open MonadReader ⦃...⦄ public

ReaderT : (R : Set a) (M : Set a → Set a) → Set a → Set a
ReaderT R M A = R → M A

module _ {R : Set a} {M : Set a → Set a} ⦃ _ : Monad M ⦄ where

  Monad-ReaderT : Monad (ReaderT R M)
  Monad-ReaderT .return a = λ r → return a
  Monad-ReaderT ._>>=_ x f = λ r → x r >>= λ a → f a r

  MonadReader-ReaderT : MonadReader (ReaderT R M) R ⦃ Monad-ReaderT ⦄
  MonadReader-ReaderT .ask = λ r → return r
  MonadReader-ReaderT .local f x = x ∘ f

  -- MonadError-ReaderT : ∀ {e} {E : Set e} → ⦃ MonadError E M ⦄ → MonadError E (ReaderT R M)
  -- MonadError-ReaderT .error e = λ r → error e
  -- MonadError-ReaderT .catch x h = λ r → catch (x r) (λ e → h e r)
