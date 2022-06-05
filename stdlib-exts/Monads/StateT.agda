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
    StateT-Monad ._>>=_ x f s = do (a' , s') ← x s; f a' s'
    StateT-Monad .return a s  = return (a , s)

    StateT-MonadState : MonadState (StateT M S) S
    StateT-MonadState .get s = return (s , s)
    StateT-MonadState .put s s' = return (tt , s)

instance
  StateT-MonadTrans : MonadTrans (λ M → StateT M S)
  StateT-MonadTrans .embed x s = (_, s) <$> x

  StateT-MonadWriter : ∀ {M W} {{_ : Monad M}} {{_ : MonadWriter M W}}
    → MonadWriter (StateT M S) W
  StateT-MonadWriter .tell w s   = tell w >>= λ _ → return (tt , s)
  StateT-MonadWriter .listen x s = listen (x s) >>= λ { ((a , s') , w) → return ((a , w) , s') }
  StateT-MonadWriter .pass x s   = x s >>= λ { (x' , s') → pass (return x') >>= λ a → return (a , s') }
