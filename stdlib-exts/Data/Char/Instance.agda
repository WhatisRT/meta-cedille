module Data.Char.Instance where

open import Class.Equality
open import Class.Show
open import Data.Char renaming (_≟_ to _≟C_)
open import Data.List
open import Data.String

instance
  Char-Eq : Eq Char
  Char-Eq = record { _≟_ = _≟C_ }

  Char-Show : Show (List Char)
  Char-Show = record { show = fromList }
