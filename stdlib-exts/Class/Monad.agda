module Class.Monad where

open import Class.Functor
open import Data.Unit
open import Level
open import Category.Monad

private
  variable
    a b : Level
    M : Set a -> Set b

record Monad (M : Set a -> Set b) : Set (suc a ⊔ b) where
  field
    _>>=_ : ∀ {A B : Set a} -> M A -> (A -> M B) -> M B
    return : ∀ {A : Set a} -> A -> M A

open Monad {{...}} public

instance
  Monad-Functor : {{_ : Monad M}} -> Functor M
  Monad-Functor = record { fmap = λ f x -> x >>= λ a -> return (f a) }

_>>_ : {A B : Set a} {{_ : Monad M}} -> M A -> M B -> M B
_>>_ x y = x >>= λ _ → y

mmap : {M : Set a -> Set a} {{_ : Monad M}} {A B : Set a} -> (A -> B) -> M A -> M B
mmap f x = do
  x' <- x
  return (f x')

join : {M : Set a -> Set a} {{_ : Monad M}} {A : Set a} -> M (M A) -> M A
join x = do
  x' <- x
  x'

void : ∀ {M : Set a -> Set b} {{_ : Monad M}} {A} -> M A -> M (Lift a ⊤)
void x = x >> return (lift tt)

toRawMonad : Monad M → RawMonad M
toRawMonad m = record { return = return {{m}} ; _>>=_ = _>>=_ {{m}} }
