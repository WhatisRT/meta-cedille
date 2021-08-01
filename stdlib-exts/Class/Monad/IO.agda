{-# OPTIONS --guardedness #-}

module Class.Monad.IO where

open import Class.Monad
open import IO
open import Level

record MonadIO {a} (M : Set a → Set a) {{_ : Monad M}} : Set (suc a) where
  field
    liftIO : ∀ {A} → IO A → M A

open MonadIO {{...}} public
