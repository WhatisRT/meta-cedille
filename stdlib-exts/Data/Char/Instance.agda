module Data.Char.Instance where

open import Agda.Builtin.Char
open import Class.Equality
open import Class.Show
open import Data.Char renaming (_≟_ to _≟C_)
open import Data.List
open import Data.String

instance
  Char-Eq : Eq Char
  Char-Eq = record { _≟_ = _≟C_ }

  Char-EqB : EqB Char
  Char-EqB = record { _≣_ = primCharEquality }

  Char-Show : Show Char
  Char-Show = record { show = λ c -> fromList [ c ] }

  CharList-Show : Show (List Char)
  CharList-Show = record { show = fromList }
