module Class.Monad where

open import Class.Functor
open import Data.Unit
open import Level

record Monad {a b} (M : Set a -> Set b) : Set (suc a ⊔ b) where
  field
    _>>=_ : ∀ {A B : Set a} -> M A -> (A -> M B) -> M B
    return : ∀ {A : Set a} -> A -> M A

open Monad {{...}} public

instance
  Monad-Functor : ∀ {a b} {M : Set a -> Set b} -> {{_ : Monad M}} -> Functor M
  Monad-Functor = record { fmap = λ f x -> x >>= λ a -> return (f a) }

_>>_ : ∀ {a b} {M : Set a -> Set b} {{_ : Monad M}} {A B : Set a} -> M A -> M B -> M B
_>>_ x y = x >>= λ _ → y

mmap : ∀ {a} {M : Set a -> Set a} {{_ : Monad M}} {A B : Set a} -> (A -> B) -> M A -> M B
mmap f x = do
  x' <- x
  return (f x')

join : ∀ {a} {M : Set a -> Set a} {{_ : Monad M}} {A : Set a} -> M (M A) -> M A
join x = do
  x' <- x
  x'

void : ∀ {a b} {M : Set a -> Set b} {{_ : Monad M}} {A} -> M A -> M (Lift a ⊤)
void x = x >> return (lift tt)

