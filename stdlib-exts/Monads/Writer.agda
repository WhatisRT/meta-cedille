module Monads.Writer where

open import Class.Monad
open import Class.Monad.Writer
open import Data.Product
open import Function

listens : ∀ {a b} {M : Set a -> Set b} {{_ : Monad M}} {A B : Set a} {W} {{_ : MonadWriter M W}}
  -> (W -> B) -> M A -> M (A × B)
listens f x = do
  (a , w) <- listen x
  return (a , f w)

censor : ∀ {a b} {M : Set a -> Set b} {{_ : Monad M}} {A : Set a} {W} {{_ : MonadWriter M W}}
  -> (W -> W) -> M A -> M A
censor f x = pass $ do
  a <- x
  return (a , f)

