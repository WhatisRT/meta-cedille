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
    A B W : Set a

WriterT : (Set a → Set a) → Set a → Set a → Set a
WriterT M W A = M (A × W)

module _ {M : Set a → Set a} {{_ : Monad M}} {W} {{_ : Monoid W}} where

  WriterT-Monad : Monad (WriterT M W)
  WriterT-Monad = record { _>>=_ = helper ; return = λ a → return (a , mzero) }
    where
      helper : WriterT M W A → (A → WriterT M W B) → WriterT M W B
      helper a f = do
        (a' , w) ← a
        (b , w') ← f a'
        return (b , w + w')

  private
    tell' : W → WriterT M W ⊤
    tell' w = return (tt , w)

    listen' : WriterT M W A → WriterT M W (A × W)
    listen' x = do
      (a , w) ← x
      return ((a , w) , w)

    pass' : WriterT M W (A × (W → W)) → WriterT M W A
    pass' x = do
      ((a , f) , w) ← x
      return (a , f w)

  WriterT-MonadWriter : MonadWriter (WriterT M W) {{WriterT-Monad}} W
  WriterT-MonadWriter = record { tell = tell' ; listen = listen' ; pass = pass' }

WriterT-MonadTrans : {W : Set a} {{_ : Monoid W}} → MonadTrans (λ (M : Set a → Set a) → WriterT M W)
WriterT-MonadTrans = record { embed = λ x → x >>= λ a → return (a , mzero) }

module _ {M : Set a → Set a} {{_ : Monad M}} {W} {{_ : Monoid W}} where

  WriterT-MonadState : ∀ {S : Set a} {{_ : MonadState M S}} → MonadState (WriterT M W) {{WriterT-Monad}} S
  WriterT-MonadState = record
    { get = embed {{WriterT-MonadTrans}} get
    ; put = embed {{WriterT-MonadTrans}} ∘ put }

  WriterT-MonadExcept : ∀ {E : Set a} {{_ : MonadExcept M E}} → MonadExcept (WriterT M W) {{WriterT-Monad}} E
  WriterT-MonadExcept = record
    { throwError = embed {{WriterT-MonadTrans}} ∘ throwError
    ; catchError = catchError }
