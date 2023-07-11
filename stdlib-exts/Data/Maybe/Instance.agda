module Data.Maybe.Instance where

open import Class.Equality
open import Class.Monad
open import Class.Show
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.String using (_++_)

instance
  Maybe-Monad : ∀ {a} -> Monad (Maybe {a})
  Maybe-Monad = record { _>>=_ = λ x f → maybe f nothing x ; return = just }

  Maybe-Eq : ∀ {A} {{_ : Eq A}} → Eq (Maybe A)
  Maybe-Eq ⦃ record { _≟_ = _≟_ } ⦄ = record { _≟_ = ≡-dec _≟_ }

  Maybe-EqB : ∀ {A} {{_ : Eq A}} → EqB (Maybe A)
  Maybe-EqB = Eq→EqB

  Maybe-Show : ∀ {a} {A : Set a} ⦃ _ : Show A ⦄ → Show (Maybe A)
  Maybe-Show .show (just x) = "just " ++ show x
  Maybe-Show .show nothing  = "nothing"
