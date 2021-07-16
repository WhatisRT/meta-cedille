module Monads.Except where

open import Class.Monad
open import Class.Monad.Except
open import Monads.ExceptT
open import Monads.Identity
open import Level

private
  variable
    a : Level
    A : Set a

Except : Set a -> Set a -> Set a
Except = ExceptT Id

instance
  Except-Monad : Monad (Except A)
  Except-Monad = ExceptT-Monad

  Except-MonadExcept : MonadExcept (Except A) A
  Except-MonadExcept = ExceptT-MonadExcept
