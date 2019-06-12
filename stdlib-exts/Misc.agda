module Misc where

open import Class.Equality
open import Data.List hiding (lookup)
open import Data.Char hiding (_≟_)
open import Data.Char.Instance
open import Relation.Unary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool hiding (_≟_)
open import Function
open import Data.Char.Ranges

open import Prelude.Strings

nameSymbols : List Char
nameSymbols = "$='-/"

nameInits : List Char
nameInits = letters ++ "_"

nameTails : List Char
nameTails = nameInits ++ nameSymbols ++ digits

toStrEscaped : Char -> List Char
toStrEscaped c = if ⌊ c ≟ '$' ⌋ ∨ ⌊ c ≟ '_' ⌋ then '\\' ∷ [ c ] else [ c ]

-- accepts the head and tail of a string and returns the head of the full string without escape symbols
unescape : Char -> List Char -> Char
unescape c r = if ⌊ c ≟ '\\' ⌋ then (case r of λ { [] → c ; (x ∷ x₁) → x}) else c

groupEscaped : List Char -> List (List Char)
groupEscaped = helper false
  where
    helper : Bool -> List Char -> List (List Char)
    helper b [] = []
    helper false (x ∷ l) = if ⌊ x ≟ '\\' ⌋ then helper true l else [ x ] ∷ helper false l
    helper true (x ∷ l) = ('\\' ∷ [ x ]) ∷ helper false l
