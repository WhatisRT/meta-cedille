module Class.Functor where

open import Level

record Functor {a b} (F : Set a -> Set b) : Set (suc a ⊔ b) where
  field
    fmap : ∀ {A B : Set a} -> (A -> B) -> F A -> F B

open Functor {{...}} public

NatTrans : ∀ {a b} (F G : Set a -> Set b) -> Set (suc a ⊔ b)
NatTrans {a} {b} F G = (A : Set a) -> F A -> G A
