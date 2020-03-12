module Data.Char.Ranges where

open import Data.Char
open import Data.List
open import Data.Nat
open import Function

charRange : ℕ -> ℕ -> List Char
charRange start amount = applyUpTo (λ x -> fromℕ $ x + start) amount

UCletters : List Char
UCletters = charRange 65 26

LCletters : List Char
LCletters = charRange 97 26

greekLCletters : List Char
greekLCletters = charRange 945 25

greekUCletters : List Char
greekUCletters = charRange 913 25

symbols : List Char
symbols =
  applyUpTo (λ x -> fromℕ $ x + 33) 15
  ++ applyUpTo (λ x -> fromℕ $ x + 58) 7
  ++ applyUpTo (λ x -> fromℕ $ x + 91) 6
  ++ applyUpTo (λ x -> fromℕ $ x + 123) 4

digits : List Char
digits = charRange 48 10

letters : List Char
letters = UCletters ++ LCletters
