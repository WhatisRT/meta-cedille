module Monads.StateT where

open import Class.Monad
open import Class.MonadTrans
open import Class.Monad.State
open import Class.Monad.Writer
open import Data.Product
open import Data.Unit
open import Function
open import Level

StateT : ∀ {a b} -> (Set a -> Set b) -> Set a -> Set a -> Set (a ⊔ b)
StateT M S A = S -> M (A × S)

module StateT {a b} {M : Set a -> Set b} {{mon : Monad M}} {S : Set a} where

  instance
    StateT-Monad : Monad (StateT M S)
    StateT-Monad = record { _>>=_ = helper ; return = λ a -> λ s -> return (a , s) }
      where
        helper : ∀ {A B} -> StateT M S A -> (A -> StateT M S B) -> StateT M S B
        helper x f = λ s -> do
          (a' , s') <- x s
          f a' s'

  private
    get' : StateT M S S
    get' = λ s -> return (s , s)

    put' : S -> StateT M S (Lift a ⊤)
    put' s = λ s' -> return (lift tt , s)

  StateT-MonadState : MonadState (StateT M S) S
  StateT-MonadState = record { get = get' ; put = put' ; state = λ f s -> return $ f s }

open StateT public

instance
  StateT-MonadTrans : ∀ {a} {S : Set a} -> MonadTrans {a} (λ M -> StateT M S)
  StateT-MonadTrans = record
    { embed = λ x -> λ s -> mmap (λ a -> (a , s)) x
    ; transform = λ τ -> λ x s -> τ _ $ x s }

  StateT-MonadWriter : ∀ {a b} {S : Set a} {M : Set a -> Set b} {{_ : Monad M}} {W}
    {{_ : MonadWriter M W}} -> MonadWriter (StateT M S) W
  StateT-MonadWriter = record
    { tell = λ w s -> tell w >>= λ _ -> return (lift tt , s)
    ; listen = λ x s -> listen (x s) >>= λ { ((a , s') , w) -> return ((a , w) , s') }
    ; pass = λ x s -> x s >>= λ { (x' , s') -> pass (return x') >>= λ a -> return (a , s') } }


