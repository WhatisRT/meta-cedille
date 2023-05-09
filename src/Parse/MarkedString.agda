--------------------------------------------------------------------------------
-- Strings with markers, used for parsing
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Parse.MarkedString where

open import Data.String using (fromList; fromChar; toList)

open import Prelude

data Marker : Set where
  NonTerminalBracket : Bool → Marker
  NameDivider : Marker
  WildcardBracket : Bool → Marker
  WildcardSeparator : Marker

instance
  Marker-Show : Show Marker
  Marker-Show = record { show = λ where
    (NonTerminalBracket true)  → "NonTerminalBracket"
    (NonTerminalBracket false) → "IgnoredNonTerminalBracket"
    NameDivider                → "NameDivider"
    (WildcardBracket true)     → "BlacklistWildcardBracket"
    (WildcardBracket false)    → "WhitelistWildcardBracket"
    WildcardSeparator          → "WildcardSeparator" }

  Marker-Eq : Eq Marker
  Marker-Eq = record { _≟_ = λ where
    (NonTerminalBracket x) (NonTerminalBracket x₁) →
      case x ≟ x₁ of λ { (yes refl) → yes refl ; (no ¬p) → no (λ { refl → ¬p refl }) }
    (NonTerminalBracket x) NameDivider → no (λ ())
    (NonTerminalBracket x) (WildcardBracket x₁) → no (λ ())
    (NonTerminalBracket x) WildcardSeparator → no (λ ())
    NameDivider (NonTerminalBracket x) → no (λ ())
    NameDivider NameDivider → yes refl
    NameDivider (WildcardBracket x) → no (λ ())
    NameDivider WildcardSeparator → no (λ ())
    (WildcardBracket x) (NonTerminalBracket x₁) → no (λ ())
    (WildcardBracket x) NameDivider → no (λ ())
    (WildcardBracket x) (WildcardBracket x₁) →
      case x ≟ x₁ of λ { (yes refl) → yes refl ; (no ¬p) → no (λ { refl → ¬p refl }) }
    (WildcardBracket x) WildcardSeparator → no (λ ())
    WildcardSeparator (NonTerminalBracket x) → no (λ ())
    WildcardSeparator NameDivider → no (λ ())
    WildcardSeparator (WildcardBracket x) → no (λ ())
    WildcardSeparator WildcardSeparator → yes refl }

  Marker-EqB = Eq→EqB {{Marker-Eq}}

enumerateMarkers : List Marker
enumerateMarkers =
  NonTerminalBracket true  ∷
  NonTerminalBracket false ∷
  NameDivider              ∷
  WildcardBracket true     ∷
  WildcardBracket false    ∷
  WildcardSeparator        ∷ []

markerRepresentation : Marker → Char
markerRepresentation (NonTerminalBracket true)  = '_'
markerRepresentation (NonTerminalBracket false) = '^'
markerRepresentation NameDivider                = '$'
markerRepresentation (WildcardBracket true)     = '!'
markerRepresentation (WildcardBracket false)    = '@'
markerRepresentation WildcardSeparator          = '&'
-- other good candidates: *#~%

MarkedChar = Char ⊎ Marker
MarkedString = List MarkedChar

markedStringToString : MarkedString → String
markedStringToString = fromList ∘ map λ where (inj₁ x) → x ; (inj₂ x) → markerRepresentation x

convertToMarked : String → MarkedString
convertToMarked = map (λ x → decCase x of
  map (λ y → (markerRepresentation y , inj₂ y)) enumerateMarkers
  default (inj₁ x)) ∘ toList
