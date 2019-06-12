module Monads.WriterT where

open import Class.Monad
open import Class.MonadTrans
open import Class.Monad.Except
open import Class.Monad.State
open import Class.Monad.Writer
open import Class.Monoid
open import Data.Product
open import Data.Unit
open import Function
open import Level

WriterT : ∀ {a b} -> (Set a -> Set b) -> Set a -> Set a -> Set b
WriterT M W A = M (A × W)

module WriterT {a b} {M : Set a -> Set b} {{mon : Monad M}} {W : Set a} {{_ : Monoid W}} where

  WriterT-Monad : Monad (WriterT M W)
  WriterT-Monad = record { _>>=_ = helper ; return = λ a -> return (a , mzero) }
    where
      helper : ∀ {A B} -> WriterT M W A -> (A -> WriterT M W B) -> WriterT M W B
      helper a f = do
        (a' , w) <- a
        (b , w') <- f a'
        return (b , w + w')

  private
    tell' : W -> WriterT M W (Lift a ⊤)
    tell' w = return (lift tt , w)

    listen' : ∀ {A} -> WriterT M W A -> WriterT M W (A × W)
    listen' x = do
      (a , w) <- x
      return ((a , w) , w)

    pass' : ∀ {A} -> WriterT M W (A × (W -> W)) -> WriterT M W A
    pass' x = do
      ((a , f) , w) <- x
      return (a , f w)

  WriterT-MonadWriter : MonadWriter (WriterT M W) {{WriterT-Monad}} W
  WriterT-MonadWriter = record { tell = tell' ; listen = listen' ; pass = pass' }

open WriterT public

WriterT-MonadTrans : ∀ {a b} {W : Set a} {{_ : Monoid W}} -> MonadTrans {a} (λ (M : Set a -> Set b) -> WriterT M W)
WriterT-MonadTrans = record { embed = λ x -> x >>= λ a -> return (a , mzero) ; transform = λ τ x -> τ _ x }

WriterT-MonadState : ∀ {a b} {S : Set a} {M : Set a -> Set b} {{_ : Monad M}} {W} {{_ : Monoid W}} {{_ : MonadState M S}} -> MonadState (WriterT M W) {{WriterT-Monad}} S
WriterT-MonadState = record
  { get = embed {{WriterT-MonadTrans}} get
  ; put = embed {{WriterT-MonadTrans}} ∘ put
  ; state = embed {{WriterT-MonadTrans}} ∘ state }

WriterT-MonadExcept : ∀ {a b} {E : Set a} {M : Set a -> Set b} {{mon : Monad M}} {W} {{_ : Monoid W}} {{_ : MonadExcept M E}} -> MonadExcept (WriterT M W) {{WriterT-Monad {{mon}}}} E
WriterT-MonadExcept = record
  { throwError = embed {{WriterT-MonadTrans}} ∘ throwError
  ; catchError = catchError }
