module Data.Tree.Base where

open import Class.Monoid
open import Class.Show
open import Data.List hiding (concat)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Instance
open import Data.String using (String; concat)
open import Data.String.Instance
open import Data.Unit
open import Function

data Tree (A : Set) : Set where
  Node : A -> List (Tree A) -> Tree A

{-# TERMINATING #-}
lengthTree : ∀ {A} -> Tree A -> ℕ
lengthTree (Node x x₁) = 1 + sum (map lengthTree x₁)

-- show tree that is compatible with org mode
{-# TERMINATING #-}
showTreeOrg : ∀ {A} {{_ : Show A}} -> Tree A -> String
showTreeOrg = helper 1
  where
    helper : ∀ {A} {{_ : Show A}} -> ℕ -> Tree A -> String
    helper level (Node x x₁) =
      (concat $ replicate level "*") + " " + show x + "\n" +
      (concat $ intersperse "\n" $ map (helper (suc level)) x₁) + "\n"
