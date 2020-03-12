module Class.Monoid where

open import Level
open import Data.List using (List; []; _∷_)

record Monoid {a} (M : Set a) : Set (suc a) where
  infixl 6 _+_
  field
    mzero : M
    _+_ : M -> M -> M

open Monoid {{...}} public

concat : ∀ {a} {M : Set a} {{_ : Monoid M}} -> List M -> M
concat [] = mzero
concat (x ∷ l) = x + concat l
