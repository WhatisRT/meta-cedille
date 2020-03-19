module Class.Map where

open import Class.Equality
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; [_])

record MapClass (K : Set) {{_ : EqB K}} (M : Set -> Set) : Set₁ where
  field
    insert : ∀ {V} -> K -> V -> M V -> M V
    remove : ∀ {V} -> K -> M V -> M V
    lookup : ∀ {V} -> K -> M V -> Maybe V
    mapSnd : ∀ {V C} -> (V -> C) -> M V -> M C
    emptyMap : ∀ {V} -> M V

open MapClass {{...}} public

mapFromList : ∀ {K V M} {{_ : EqB K}} {{_ : MapClass K M}} -> (V -> K) -> List V -> M (List V)
mapFromList f [] = emptyMap
mapFromList f (x ∷ l) with mapFromList f l
... | m with lookup (f x) m
... | just x₁ = insert (f x) (x ∷ x₁) m
... | nothing = insert (f x) [ x ] m
