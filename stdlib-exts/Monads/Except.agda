module Monads.Except where

open import Class.Monad
open import Class.Monad.Except
open import Monads.ExceptT
open import Monads.Identity

Except : ∀ {a} -> Set a -> Set a -> Set a
Except = ExceptT Id

instance
  Except-Monad : ∀ {a} {A : Set a} -> Monad (Except A)
  Except-Monad = ExceptT-Monad {{Id-Monad}}

  Except-MonadExcept : ∀ {a} {A : Set a} -> MonadExcept (Except A) A
  Except-MonadExcept = ExceptT-MonadExcept {{Id-Monad}}
