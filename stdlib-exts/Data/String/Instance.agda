module Data.String.Instance where

open import Agda.Builtin.String
open import Class.Equality
open import Class.Monoid
open import Class.Show
open import Data.String renaming (_≟_ to _≟S_)

instance
  String-Eq : Eq String
  String-Eq = record { _≟_ = _≟S_ }

  String-EqB : EqB String
  String-EqB = record { _≣_ = primStringEquality }

  String-Monoid : Monoid String
  String-Monoid = record { mzero = "" ; _+_ = _++_ }

  String-Show : Show String
  String-Show = record { show = λ x -> x }
