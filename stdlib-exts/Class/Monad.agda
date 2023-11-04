module Class.Monad where

open import Category.Monad renaming (RawMonad to Monad) public
open import Class.Functor
open import Data.Bool
open import Data.Unit.Polymorphic

open Monad {{...}} using (return; _>>=_; _=<<_; _>>_; _>=>_; _<=<_) public

module _ {a} {M : Set a → Set a} {{m : Monad M}} where

  instance
    _ = Monad.rawIApplicative m
    monadFunctor = Monad.rawFunctor m

  infix 0 mif_then_
  mif_then_ : Bool → M ⊤ → M ⊤
  mif b then x = if b then x else return _

  void : ∀ {A} → M A → M ⊤
  void x = x >> return tt

  _<$₂>_,_ : ∀ {A B C} → (A → B → C) → M A → M B → M C
  f <$₂> x , y = do x ← x; y ← y; return (f x y)
