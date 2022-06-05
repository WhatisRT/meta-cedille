module Monads.WriterT where

open import Class.Monad
open import Class.MonadTrans
open import Class.Monad.Except
open import Class.Monad.State
open import Class.Monad.Writer
open import Class.Monoid
open import Data.Product
open import Data.Unit.Polymorphic
open import Function
open import Level

private
  variable
    a : Level
    A B E S W : Set a

WriterT : (Set a → Set a) → Set a → Set a → Set a
WriterT M W A = M (A × W)

module _ {M : Set a → Set a} {{_ : Monad M}} {W} {{_ : Monoid W}} where

  WriterT-Monad : Monad (WriterT M W)
  WriterT-Monad ._>>=_ a f = do (a' , w) ← a; (b , w') ← f a'; return (b , w + w')
  WriterT-Monad .return a = return (a , mzero)

  WriterT-MonadWriter : MonadWriter (WriterT M W) {{WriterT-Monad}} W
  WriterT-MonadWriter .tell w = return (tt , w)
  WriterT-MonadWriter .listen x = do (a , w) ← x; return ((a , w) , w)
  WriterT-MonadWriter .pass x = do ((a , f) , w) ← x; return (a , f w)

WriterT-MonadTrans : {{_ : Monoid W}} → MonadTrans (λ (M : Set a → Set a) → WriterT M W)
WriterT-MonadTrans .embed x = x >>= λ a → return (a , mzero)

module _ {M : Set a → Set a} {{_ : Monad M}} {W} {{_ : Monoid W}} where

  WriterT-MonadState : {{_ : MonadState M S}} → MonadState (WriterT M W) {{WriterT-Monad}} S
  WriterT-MonadState .get = embed {{WriterT-MonadTrans}} get
  WriterT-MonadState .put = embed {{WriterT-MonadTrans}} ∘ put

  WriterT-MonadExcept : {{_ : MonadExcept M E}} → MonadExcept (WriterT M W) {{WriterT-Monad}} E
  WriterT-MonadExcept .throwError = embed {{WriterT-MonadTrans}} ∘ throwError
  WriterT-MonadExcept .catchError = catchError
