module Class.Map where

open import Class.Equality
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; [_])

record MapClass (M : Set -> Set -> Set) : Set₁ where
  field
    insert : ∀ {A B} {{_ : EqB A}} -> A -> B -> M A B -> M A B
    remove : ∀ {A B} {{_ : EqB A}} -> A -> M A B -> M A B
    lookup : ∀ {A B} {{_ : EqB A}} -> A -> M A B -> Maybe B
    mapSnd : ∀ {A B C} -> (B -> C) -> M A B -> M A C
    emptyMap : ∀ {A B} -> M A B

open MapClass {{...}} public

mapFromList : ∀ {A B} {M} {{_ : MapClass M}} {{_ : EqB B}} -> (A -> B) -> List A -> M B (List A)
mapFromList f [] = emptyMap
mapFromList f (x ∷ l) with mapFromList f l
... | m with lookup (f x) m
... | just x₁ = insert (f x) (x ∷ x₁) m
... | nothing = insert (f x) [ x ] m
