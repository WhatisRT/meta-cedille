{-# OPTIONS --type-in-type #-}

module IO.Instance where

open import Class.Monad using (Monad)
open import Class.Monad.IO
open import Class.Monoid
open import Codata.Musical.Notation
open import Data.Product
open import Data.Sum
open import IO
open import Monads.ExceptT
open import Monads.StateT
open import Monads.WriterT
open import Level

instance
  IO-Monad : Monad IO
  IO-Monad = record { _>>=_ = λ x f -> (♯ x) >>= λ a -> ♯ f a ; return = return }

  IO-MonadIO : MonadIO IO
  IO-MonadIO = record { liftIO = λ x -> x }

module _ {a} {M : Set a -> Set a} {{_ : Monad M}} {{_ : MonadIO M}} where
  
  ExceptT-MonadIO : ∀ {E} -> MonadIO (ExceptT M E) {{ExceptT-Monad}}
  ExceptT-MonadIO = record { liftIO = λ x -> liftIO (♯ x >>= λ a -> ♯ return (inj₂ a)) }
  
  StateT-MonadIO : ∀ {S} -> MonadIO (StateT M S)
  StateT-MonadIO = record { liftIO = λ x -> λ s -> liftIO (♯ x >>= (λ a -> ♯ return (a , s))) }
  
  WriterT-MonadIO : ∀ {W} {{_ : Monoid W}} -> MonadIO (WriterT M W) {{WriterT-Monad}}
  WriterT-MonadIO = record { liftIO = λ x -> liftIO (♯ x >>= λ a -> ♯ return (a , mzero)) }
  
