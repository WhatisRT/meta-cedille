module Class.Monad.State where

open import Class.Monad
open import Data.Product
open import Data.Unit.Polymorphic
open import Function
open import Level

private
  variable
    a : Level
    A : Set a

record MonadState {a} (M : Set a → Set a) {{_ : Monad M}} (S : Set a) : Set (suc a) where
  field
    get : M S
    put : S → M ⊤

  modify : (S → S) → M ⊤
  modify f = do
    s <- get
    put (f s)

  gets : (S → A) → M A
  gets f = do
    s <- get
    return (f s)

  state : (S → A × S) → M A
  state f = do
    s ← get
    let (a , s') = f s
    put s'
    return a

open MonadState {{...}} public

module _ {M : Set a → Set a} {{_ : Monad M}} {S S' : Set a} {{_ : MonadState M (S × S')}} where

  MonadStateProj₁ : MonadState M S
  MonadStateProj₁ = record
    { get = get >>= return ∘ proj₁
    ; put = λ x → modify λ { (s , s') → (x , s') } }

  MonadStateProj₂ : MonadState M S'
  MonadStateProj₂ = record
    { get = get >>= return ∘ proj₂
    ; put = λ x → modify λ { (s , s') → (s , x) } }
