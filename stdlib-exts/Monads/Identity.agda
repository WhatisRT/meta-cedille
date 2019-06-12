module Monads.Identity where

open import Class.Functor
open import Class.Monad
open import Class.MonadTrans

Id : ∀ {a} -> Set a -> Set a
Id A = A

IdentityT : ∀ {a b} -> (Set a -> Set b) -> Set a -> Set b
IdentityT M A = M A

Id-Monad : ∀ {a} -> Monad (Id {a})
Id-Monad = record { _>>=_ = λ a f -> f a ; return = λ a -> a }

module Internal {a b} (M : Set a -> Set b) {{_ : Monad M}} where
  IdentityT-Monad : Monad (IdentityT M)
  IdentityT-Monad = record { _>>=_ = _>>=_ ; return = return }

return-NatTrans : ∀ {a} {M : Set a -> Set a} {{mon : Monad M}} -> NatTrans Id M
return-NatTrans = λ A x → return x
