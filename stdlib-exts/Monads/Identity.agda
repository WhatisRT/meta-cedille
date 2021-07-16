module Monads.Identity where

open import Class.Functor
open import Class.Monad
open import Class.MonadTrans
open import Level

private
  variable
    a : Level

Id : Set a -> Set a
Id A = A

IdentityT : (Set a -> Set a) -> Set a -> Set a
IdentityT M A = M A

instance
  Id-Monad : Monad (Id {a})
  Id-Monad = record { _>>=_ = λ a f -> f a ; return = λ a -> a }

module _ (M : Set a -> Set a) {{_ : Monad M}} where
  IdentityT-Monad : Monad (IdentityT M)
  IdentityT-Monad = record { _>>=_ = _>>=_ ; return = return }
