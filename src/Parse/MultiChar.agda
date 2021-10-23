--------------------------------------------------------------------------------
-- White or blacklisting of characters
--------------------------------------------------------------------------------

module Parse.MultiChar where

import Data.List.NonEmpty as NE
open import Data.List hiding (uncons)
open import Data.String hiding (show)

open import Prelude

-- TODO: Groups of characters, such as digits or lower case letters
MultiCharGroup : Set
MultiCharGroup = ⊥

matchCharGroup : MultiCharGroup → Char → Bool
matchCharGroup ()

data CharMatcher : Set where
  Single : Char → CharMatcher
  Group  : MultiCharGroup → CharMatcher

instance
  CharMatcher-Show : Show CharMatcher
  CharMatcher-Show = record { show = helper }
    where
      helper : CharMatcher → String
      helper (Single c) = fromChar c

parseCharMatcher : String → Maybe CharMatcher
parseCharMatcher s with uncons s
... | just (c , "") = just (Single c)
... | _             = nothing

matchCharMatcher : CharMatcher → Char → Bool
matchCharMatcher (Single x) c = x ≣ c
matchCharMatcher (Group  g) c = matchCharGroup g c

record MultiChar : Set where
  field
    matches : List CharMatcher
    negated : Bool

instance
  MultiChar-Show : Show MultiChar
  MultiChar-Show = record { show = helper }
    where
      helper : MultiChar → String
      helper m = (if negated then "!" else "") + show matches
        where open MultiChar m

parseMultiChar : Bool → List String → MultiChar
parseMultiChar b l = record { matches = mapMaybe parseCharMatcher l ; negated = b }

parseMultiCharNE : Bool → NE.List⁺ String → MultiChar
parseMultiCharNE b l = parseMultiChar b (NE.toList l)

matchMulti : MultiChar → Char → Bool
matchMulti m c = negated xor (or $ map (flip matchCharMatcher c) matches)
  where open MultiChar m
