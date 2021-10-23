--------------------------------------------------------------------------------
-- Strings with markers, used for parsing
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Parse.MarkedString where

open import Data.String hiding (_≟_)

open import Prelude

data Marker : Set where
  NonTerminalBracket : Marker
  NameDivider : Marker
  BlacklistWildcardBracket : Marker
  WhitelistWildcardBracket : Marker
  WildcardSeparator : Marker

instance
  Marker-Show : Show Marker
  Marker-Show = record { show = λ
    { NonTerminalBracket → "NonTerminalBracket"
    ; NameDivider → "NameDivider"
    ; BlacklistWildcardBracket → "BlacklistWildcardBracket"
    ; WhitelistWildcardBracket → "WhitelistWildcardBracket"
    ; WildcardSeparator → "WildcardSeparator"} }

  Marker-Eq : Eq Marker
  Marker-Eq = record { _≟_ = λ
    { NonTerminalBracket NonTerminalBracket → yes refl
    ; NonTerminalBracket NameDivider → no λ ()
    ; NonTerminalBracket BlacklistWildcardBracket → no λ ()
    ; NonTerminalBracket WhitelistWildcardBracket → no λ ()
    ; NonTerminalBracket WildcardSeparator → no λ ()
    ; NameDivider NonTerminalBracket → no λ ()
    ; NameDivider NameDivider → yes refl
    ; NameDivider BlacklistWildcardBracket → no λ ()
    ; NameDivider WhitelistWildcardBracket → no λ ()
    ; NameDivider WildcardSeparator → no λ ()
    ; BlacklistWildcardBracket NonTerminalBracket → no λ ()
    ; BlacklistWildcardBracket NameDivider → no λ ()
    ; BlacklistWildcardBracket BlacklistWildcardBracket → yes refl
    ; BlacklistWildcardBracket WhitelistWildcardBracket → no λ ()
    ; BlacklistWildcardBracket WildcardSeparator → no λ ()
    ; WhitelistWildcardBracket NonTerminalBracket → no λ ()
    ; WhitelistWildcardBracket NameDivider → no λ ()
    ; WhitelistWildcardBracket BlacklistWildcardBracket → no λ ()
    ; WhitelistWildcardBracket WhitelistWildcardBracket → yes refl
    ; WhitelistWildcardBracket WildcardSeparator → no λ ()
    ; WildcardSeparator NonTerminalBracket → no λ ()
    ; WildcardSeparator NameDivider → no λ ()
    ; WildcardSeparator BlacklistWildcardBracket → no λ ()
    ; WildcardSeparator WhitelistWildcardBracket → no λ ()
    ; WildcardSeparator WildcardSeparator → yes refl} }

  Marker-EqB = Eq→EqB {{Marker-Eq}}

enumerateMarkers : List Marker
enumerateMarkers =
  NonTerminalBracket ∷
  NameDivider ∷
  BlacklistWildcardBracket ∷
  WhitelistWildcardBracket ∷
  WildcardSeparator ∷ []

markerRepresentation : Marker → Char
markerRepresentation NonTerminalBracket = '_'
markerRepresentation NameDivider = '$'
markerRepresentation BlacklistWildcardBracket = '!'
markerRepresentation WhitelistWildcardBracket = '@'
markerRepresentation WildcardSeparator = '&'
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
