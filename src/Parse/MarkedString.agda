--------------------------------------------------------------------------------
-- Strings with markers, used for parsing
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Parse.MarkedString where

open import Prelude

open import Class.Listable
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.String using (fromList; fromChar; toList)

data Marker : Set where
  NonTerminalBracket : Bool → Marker
  NameDivider : Marker
  WildcardBracket : Bool → Marker
  WildcardSeparator : Marker

markerRepresentation : Marker → Char
markerRepresentation (NonTerminalBracket true)  = '_'
markerRepresentation (NonTerminalBracket false) = '^'
markerRepresentation NameDivider                = '$'
markerRepresentation (WildcardBracket true)     = '!'
markerRepresentation (WildcardBracket false)    = '@'
markerRepresentation WildcardSeparator          = '&'
-- other good candidates: *#~%

instance
  Marker-Show : Show Marker
  Marker-Show .show (NonTerminalBracket true)  = "NonTerminalBracket"
  Marker-Show .show (NonTerminalBracket false) = "IgnoredNonTerminalBracket"
  Marker-Show .show NameDivider                = "NameDivider"
  Marker-Show .show (WildcardBracket true)     = "BlacklistWildcardBracket"
  Marker-Show .show (WildcardBracket false)    = "WhitelistWildcardBracket"
  Marker-Show .show WildcardSeparator          = "WildcardSeparator"

  Marker-Listable : Listable Marker
  Marker-Listable = record
    { listing = (NonTerminalBracket true) ∷ (NonTerminalBracket false) ∷
        NameDivider ∷ (WildcardBracket true) ∷ (WildcardBracket false) ∷ WildcardSeparator ∷ []
    ; complete = λ where
        (NonTerminalBracket true)  → pf 0 (here refl)
        (NonTerminalBracket false) → pf 1 (here refl)
        NameDivider                → pf 2 (here refl)
        (WildcardBracket true)     → pf 3 (here refl)
        (WildcardBracket false)    → pf 4 (here refl)
        WildcardSeparator          → pf 5 (here refl) }
    where pf = listable-pf-helper

  Marker-Eq : Eq Marker
  Marker-Eq = Listable.Listable→Eq Marker-Listable

  Marker-EqB = Eq→EqB {{Marker-Eq}}

MarkedString = List (Char ⊎ Marker)

markedStringToString : MarkedString → String
markedStringToString = fromList ∘ map λ where (inj₁ x) → x ; (inj₂ x) → markerRepresentation x

convertToMarked : String → MarkedString
convertToMarked = map (λ x → decCase x of
  map (λ y → (markerRepresentation y , inj₂ y)) (Listable.listing Marker-Listable)
  default (inj₁ x)) ∘ toList
