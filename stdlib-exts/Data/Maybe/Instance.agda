module Data.Maybe.Instance where

open import Class.Monad
open import Data.Maybe

instance
  Maybe-Monad : ∀ {a} -> Monad (Maybe {a})
  Maybe-Monad = record { _>>=_ = λ x f → maybe f nothing x ; return = just }
