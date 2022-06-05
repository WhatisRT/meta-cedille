--------------------------------------------------------------------------------
-- This file provides functions for escaping
--------------------------------------------------------------------------------

module Parse.Escape where

open import Class.Map
open import Data.SimpleMap
open import Data.Map.Char
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
    ("ampersand" , '&') ∷ ("backslash" , '\\') ∷ ("slash" , '/') ∷ ("pipe" , '|') ∷ ("circumflex" , '^') ∷
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

  escapeTable : CharMap String
  escapeTable = fromListCM $ map swap translationTable

  isSpecialChar : Char → Bool
  isSpecialChar c = c ≣ '$' ∨ c ≣ '_' ∨ c ≣ '!' ∨ c ≣ '@' ∨ c ≣ '&' ∨ c ≣ '^'

-- accepts the head and tail of a string and returns the head of the full string without escape symbols
unescape : Char → String → Char
unescape c r = if ⌊ c ≟ '\\' ⌋ then (case strHead r of λ { nothing → c ; (just x) → x }) else c

groupEscaped : List Char → List (List Char)
groupEscaped = helper false
  where
    helper : Bool → List Char → List (List Char)
    helper b [] = []
    helper false (x ∷ l) = if ⌊ x ≟ '\\' ⌋ then helper true l else [ x ] ∷ helper false l
    helper true (x ∷ l) = ('\\' ∷ [ x ]) ∷ helper false l

translate : List Char → Maybe (List Char)
translate = helper ∘ splitMulti '='
  where
    helper : List (List Char) → Maybe (List Char)
    helper [] = just []
    helper (l ∷ []) = just l
    helper (l ∷ l₁ ∷ l₂) = do
      l' ← lookup (fromList l₁) translationTable
      l'' ← helper l₂
      return $ l + (if isSpecialChar l' then '\\' ∷ [ l' ] else [ l' ]) + l''

translateS : String → Maybe String
translateS s = fromList <$> (translate $ toList s)

escapeChar : Char → List Char
escapeChar c = maybe (λ s → "=" ++ toList s ++ "=") [ c ] $ lookup c escapeTable

ruleToConstr : String → String
ruleToConstr = fromList ∘ concat ∘ helper ∘ groupEscaped ∘ toList
  where
    helper : List (List Char) → List (List Char)
    helper [] = []
    helper (l ∷ l₁) = (case l of λ where
      (c ∷ []) → if isSpecialChar c
        then [ c ]
        else escapeChar c
      ('\\' ∷ c ∷ []) → if isSpecialChar c
        then escapeChar c
        else l
      _ → l) ∷ (helper l₁)
