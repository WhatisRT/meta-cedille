--------------------------------------------------------------------------------
-- This file provides functions for escaping
--------------------------------------------------------------------------------

module Parse.Escape where

import Data.Sum
open import Class.Map
open import Data.SimpleMap
open import Data.Map.Char
open import Data.String using (fromList; toList)

open import Prelude
open import Prelude.Strings

open import Parse.MarkedString

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

translateMarked : MarkedString → Maybe MarkedString
translateMarked = helper ∘ splitMulti (inj₁ '=')
  where
    lookupTranslation : MarkedString → Maybe Char
    lookupTranslation s = do
      s' ← traverse Data.Sum.[ just , (λ _ → nothing) ] s
      lookup (fromList s') translationTable

    helper : List MarkedString → Maybe MarkedString
    helper [] = just []
    helper (l ∷ []) = just l
    helper (l ∷ l₁ ∷ l₂) = do
      l' ← lookupTranslation l₁
      l'' ← helper l₂
      return $ l + [ inj₁ l' ] + l''

escapeChar : Char → List Char
escapeChar c = maybe (λ s → "=" ++ toList s ++ "=") [ c ] $ lookup c escapeTable

ruleToConstr : MarkedString → String
ruleToConstr = fromList ∘ concat ∘ map Data.Sum.[ escapeChar , [_] ∘ markerRepresentation ]

translateS : String → Maybe String
translateS s = markedStringToString <$> (translateMarked $ convertToMarked s)
