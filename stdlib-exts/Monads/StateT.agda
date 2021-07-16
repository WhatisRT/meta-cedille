module Monads.StateT where

open import Class.Monad
open import Class.Functor
open import Class.MonadTrans
open import Class.Monad.State
open import Class.Monad.Writer
open import Data.Product
open import Data.Unit.Polymorphic
open import Function
open import Level

private
  variable
    a : Level
    S : Set a

StateT : (Set a → Set a) → Set a → Set a → Set (a)
StateT M S A = S → M (A × S)

module _ {M : Set a → Set a} {{_ : Monad M}} {S} where

  instance
    StateT-Monad : Monad (StateT M S)
    StateT-Monad = record { _>>=_ = helper ; return = λ a → λ s → return (a , s) }
      where
        helper : ∀ {A B} → StateT M S A → (A → StateT M S B) → StateT M S B
        helper x f = λ s → do
          (a' , s') ← x s
          f a' s'

    StateT-MonadState : MonadState (StateT M S) S
    MonadState.get StateT-MonadState s = return (s , s)
    MonadState.put StateT-MonadState s = λ s' → return (tt , s)

instance
  StateT-MonadTrans : MonadTrans (λ M → StateT M S)
  StateT-MonadTrans = record { embed = λ x s → (_, s) <$> x }

  StateT-MonadWriter : ∀ {M W} {{_ : Monad M}} {{_ : MonadWriter M W}}
    → MonadWriter (StateT M S) W
  StateT-MonadWriter = record
    { tell = λ w s → tell w >>= λ _ → return (tt , s)
    ; listen = λ x s → listen (x s) >>= λ { ((a , s') , w) → return ((a , w) , s') }
    ; pass = λ x s → x s >>= λ { (x' , s') → pass (return x') >>= λ a → return (a , s') } }
