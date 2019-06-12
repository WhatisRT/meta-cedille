module Class.MonadTrans where

open import Class.Functor
open import Class.Monad
open import Level

record MonadTrans {a b} (T : (Set a -> Set b) -> Set a -> Set b) : Set (suc a ⊔ suc b) where
  field
    embed : {A : Set a} {M : Set a -> Set b} {{_ : Monad M}} -> M A -> T M A
    transform : {A : Set a} {M M' : Set a -> Set b} -> NatTrans M M' -> T M A -> T M' A

open MonadTrans {{...}} public
