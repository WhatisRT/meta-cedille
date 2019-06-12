module Class.Monad.State where

  open import Class.Monad
  open import Data.Product
  open import Data.Unit
  open import Function
  open import Level

  record MonadState {a b} (M : Set a -> Set b) {{_ : Monad M}} (S : Set a) : Set (suc a ⊔ b) where
    field
      get : M S
      put : S -> M (Lift a ⊤)
      state : ∀ {A} -> (S -> A × S) -> M A

  open MonadState {{...}} public

  modify : ∀ {a b} {M : Set a -> Set b} {{_ : Monad M}} {S} {{_ : MonadState M S}} -> (S -> S) -> M (Lift a ⊤)
  modify f = do
    s <- get
    put (f s)

  gets : ∀ {a b} {M : Set a -> Set b} {{_ : Monad M}} {A} {S} {{_ : MonadState M S}} -> (S -> A) -> M A
  gets f = do
    s <- get
    return (f s)

  MonadStateProj₁ : ∀ {a b} {M : Set a -> Set b} {{_ : Monad M}} {S S' : Set a} {{_ : MonadState M (S × S')}} -> MonadState M S
  MonadStateProj₁ = record
    { get = get >>= (return ∘ proj₁)
    ; put = λ x -> modify λ { (s , s') -> (x , s')}
    ; state = λ f -> state λ { (s , s') -> case f s of λ { (a , s₁) -> a , s₁ , s' } } }

  MonadStateProj₂ : ∀ {a b} {M : Set a -> Set b} {{_ : Monad M}} {S S' : Set a} {{_ : MonadState M (S × S')}} -> MonadState M S'
  MonadStateProj₂ = record
    { get = get >>= (return ∘ proj₂)
    ; put = λ x -> modify λ { (s , s') -> (s , x)}
    ; state = λ f -> state λ { (s , s') -> case f s' of λ { (a , s₁) -> a , s , s₁ } } }
