module Class.Monoid where

open import Level

record Monoid {a} (M : Set a) : Set (suc a) where
  infixl 6 _+_
  field
    mzero : M
    _+_ : M -> M -> M

open Monoid {{...}} public
