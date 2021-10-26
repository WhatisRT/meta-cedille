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
-- other good candidates: &*#~%

escapeMarker = '\\'

MarkedChar = Char ⊎ Marker
MarkedString = List MarkedChar

markedStringToString : MarkedString → String
markedStringToString [] = ""
markedStringToString (inj₁ x ∷ s) =
  fromList (decCase x of
    map (λ x → (x , escapeMarker ∷ [ x ])) $
      -- if we find anything in this list, escape it
      escapeMarker ∷ map markerRepresentation enumerateMarkers
    default [ x ])
    + markedStringToString s
markedStringToString (inj₂ x ∷ s) = (fromChar $ markerRepresentation x) + markedStringToString s

convertToMarked : String → MarkedString
convertToMarked s = helper false (toList s)
  where
    -- first argument is whether the current character is escaped
    helper : Bool → List Char → MarkedString
    helper _     []      = []
    helper false (x ∷ l) =
      decCase x of
        (escapeMarker , helper true l) ∷
        map (λ y → (markerRepresentation y , inj₂ y ∷ helper false l)) enumerateMarkers
        default (inj₁ x ∷ helper false l)
    helper true  (x ∷ l) = inj₁ x ∷ helper false l
