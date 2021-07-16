module Data.Maybe.Instance where

open import Class.Equality
open import Class.Monad
open import Data.Maybe
open import Data.Maybe.Properties

instance
  Maybe-Monad : ∀ {a} -> Monad (Maybe {a})
  Maybe-Monad = record { _>>=_ = λ x f → maybe f nothing x ; return = just }

  Maybe-Eq : ∀ {A} {{_ : Eq A}} → Eq (Maybe A)
  Maybe-Eq ⦃ record { _≟_ = _≟_ } ⦄ = record { _≟_ = ≡-dec _≟_ }
