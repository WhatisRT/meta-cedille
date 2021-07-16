module Class.Monad.Except where

open import Class.Monad
open import Class.Monoid
open import Data.Maybe
open import Level

private
  variable
    a : Level
    A : Set a

record MonadExcept (M : Set a → Set a) {{_ : Monad M}} (E : Set a) : Set (suc a) where
  field
    throwError : E → M A
    catchError : M A → (E → M A) → M A

  appendIfError : {{_ : Monoid E}} → M A → E → M A
  appendIfError x s = catchError x λ e → throwError (e + s)

  maybeToError : Maybe A → E → M A
  maybeToError (just x) e = return x
  maybeToError nothing e = throwError e

  tryElse : M A → M A → M A
  tryElse x y = catchError x λ _ → y

open MonadExcept {{...}} public
