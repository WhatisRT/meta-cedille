module Data.Tree.Instance where

open import Class.Functor
open import Class.Monad
open import Class.Monoid
open import Class.Show
open import Class.Traversable
open import Data.List
open import Data.List.Instance
open import Data.String using (String)
open import Data.String.Instance
open import Data.Tree.Base
open import Misc

instance
  {-# TERMINATING #-}
  Tree-Functor : Functor Tree
  Tree-Functor = record { fmap = helper }
    where
      helper : ∀ {A B} -> (A -> B) -> Tree A -> Tree B
      helper f (Node x x₁) = Node (f x) (map (helper f) x₁)

  {-# TERMINATING #-}
  Tree-Show : ∀ {A} {{_ : Show A}} -> Show (Tree A)
  Tree-Show = record { show = helper show }
    where
      helper : ∀ {A} -> (A -> String) -> Tree A -> String
      helper f (Node x x₁) = "Node (" + f x + ") " + show (map (helper f) x₁)

  {-# TERMINATING #-}
  Tree-Traversable : Traversable Tree
  Tree-Traversable = record { sequence = helper }
    where
      helper : {M : Set → Set} {{_ : Monad M}} {A : Set} → Tree (M A) → M (Tree A)
      helper (Node x y) = do
        x' <- x
        y' <- sequence (map helper y)
        return (Node x' y')
