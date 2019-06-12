module Class.Monad.Except where

open import Class.Monad
open import Class.Monoid
open import Data.Maybe
open import Level

record MonadExcept {a b} (M : Set a -> Set b) {{_ : Monad M}} (E : Set a) : Set (suc a ⊔ b) where
  field
    throwError : ∀ {A} -> E -> M A
    catchError : ∀ {A} -> M A -> (E -> M A) -> M A

open MonadExcept {{...}} public

module Except-Internal {a b} {A E : Set a} {M : Set a -> Set b} {{_ : Monad M}} {{_ : MonadExcept M E}} where

  appendIfError : {{_ : Monoid E}} -> M A -> E -> M A
  appendIfError x s = catchError x λ e -> throwError (e + s)

  maybeToError : Maybe A -> E -> M A
  maybeToError (just x) e = return x
  maybeToError nothing e = throwError e

  tryElse : M A -> M A -> M A
  tryElse x y = catchError x λ _ -> y

open Except-Internal public
