--------------------------------------------------------------------------------
-- White or blacklisting of characters
--------------------------------------------------------------------------------

module Parse.MultiChar where

open import Prelude

import Data.List.NonEmpty as NE

parseCharMatcher : String → Maybe Char
parseCharMatcher s with uncons s
... | just (c , "") = just c
... | _             = nothing

record MultiChar : Set where
  field
    matches : List Char
    negated : Bool

instance
  MultiChar-Show : Show MultiChar
  MultiChar-Show .show m = (if negated then "!" else "") + show ⦃ List-Show ⦄ matches
    where open MultiChar m

parseMultiChar : Bool → List String → MultiChar
parseMultiChar b l = record { matches = mapMaybe parseCharMatcher l ; negated = b }

parseMultiCharNE : Bool → NE.List⁺ String → MultiChar
parseMultiCharNE b l = parseMultiChar b (NE.toList l)

matchMulti : MultiChar → Char → Bool
matchMulti m c = negated xor (or $ map (c ≣_) matches)
  where open MultiChar m
