--------------------------------------------------------------------------------
-- This file provides functions for escaping
--------------------------------------------------------------------------------

module Escape where

open import Class.Map
open import Data.SimpleMap
open import Data.String using (fromList; toList)

open import Prelude
open import Prelude.Strings

private
  translationTable : SimpleMap String Char
  translationTable =
    ("newline" , '\n') ∷ ("space" , ' ') ∷ ("ast" , '*') ∷ ("sq" , '□') ∷
    ("lparen" , '(') ∷ ("rparen" , ')') ∷ ("lbrace" , '{') ∷ ("rbrace" , '}') ∷
    ("lsquare" , '[') ∷ ("rsquare" , ']') ∷ ("langle" , '<') ∷ ("rangle" , '>') ∷
    ("equal" , '=') ∷ ("dot" , '.') ∷ ("comma" , ',') ∷ ("colon" , ':') ∷ ("semicolon" , ';') ∷
    ("question" , '?') ∷ ("exclamation" , '!') ∷ ("at" , '@') ∷ ("doublequote" , '"') ∷
    ("ampersand" , '&') ∷ ("backslash" , '\\') ∷ ("slash" , '/') ∷ ("pipe" , '|') ∷
    ("underscore" , '_') ∷ ("dollar" , '$') ∷ ("minus" , '-') ∷ ("forall" , '∀') ∷ ("exists" , '∃') ∷
    ("alpha" , 'α') ∷ ("beta" , 'β') ∷ ("gamma" , 'γ') ∷ ("delta" , 'δ') ∷ ("epsilon" , 'ε') ∷
    ("zeta" , 'ζ') ∷ ("eta" , 'η') ∷ ("theta" , 'θ') ∷ ("iota" , 'ι') ∷ ("kappa" , 'κ') ∷
    ("lambda" , 'λ') ∷ ("mu" , 'μ') ∷ ("nu" , 'ν') ∷ ("xi" , 'ξ') ∷ ("omicron" , 'ο') ∷ ("pi" , 'π') ∷
    ("rho" , 'ρ') ∷ ("varsigma" , 'ς') ∷ ("sigma" , 'σ') ∷ ("tau" , 'τ') ∷ ("upsilon" , 'υ') ∷
    ("phi" , 'φ') ∷ ("chi" , 'χ') ∷ ("psi" , 'ψ') ∷ ("omega" , 'ω') ∷
    ("Alpha" , 'Α') ∷ ("Beta" , 'Β') ∷ ("Gamma" , 'Γ') ∷ ("Delta" , 'Δ') ∷ ("Epsilon" , 'Ε') ∷
    ("Zeta" , 'Ζ') ∷ ("Eta" , 'Η') ∷ ("Theta" , 'Θ') ∷ ("Iota" , 'Ι') ∷ ("Kappa" , 'Κ') ∷
    ("Lambda" , 'Λ') ∷ ("Mu" , 'Μ') ∷ ("Nu" , 'Ν') ∷ ("Xi" , 'Ξ') ∷ ("Omicron" , 'Ο') ∷
    ("Pi" , 'Π') ∷ ("Rho" , 'Ρ') ∷ ("Varsigma" , 'Σ') ∷ ("Sigma" , 'Σ') ∷ ("Tau" , 'Τ') ∷
    ("Upsilon" , 'Υ') ∷ ("Phi" , 'Φ') ∷ ("Chi" , 'Χ') ∷ ("Psi" , 'Ψ') ∷ ("Omega" , 'Ω') ∷
    []

  escapeTable : SimpleMap Char String
  escapeTable = map swap translationTable

groupEscaped : List Char → List (List Char)
groupEscaped = helper false
  where
    helper : Bool → List Char → List (List Char)
    helper b [] = []
    helper false (x ∷ l) = if ⌊ x ≟ '\\' ⌋ then helper true l else [ x ] ∷ helper false l
    helper true (x ∷ l) = ('\\' ∷ [ x ]) ∷ helper false l

translate : List Char → Maybe (List Char)
translate = (concat <$>_) ∘ helper ∘ splitMulti '='
  where
    helper : List (List Char) → Maybe (List (List Char))
    helper [] = just []
    helper (l ∷ []) = just (l ∷ [])
    helper (l ∷ l₁ ∷ l₂) = do
      l' ← (lookup (fromList l₁) translationTable)
      l'' ← helper l₂
      return $ l ∷
        (decCase l' of
          ('_' , "\\_") ∷ ('$' , "\\$") ∷ ('!' , "\\!") ∷ ('@' , "\\@") ∷ ('&' , "\\&") ∷ []
          default [ l' ]) ∷ l''

escapeChar : Char → List Char
escapeChar c = maybe (λ s → "=" ++ toList s ++ "=") [ c ] $ lookup c escapeTable
