module Data.List.Instance where

open import Class.Equality
open import Class.Monad
open import Class.Monoid
open import Class.Show
open import Class.Traversable
open import Data.Bool using (Bool; _∧_; true; false)
open import Data.List hiding (concat)
open import Data.List.Properties
open import Data.String using (String)
open import Data.String.Instance
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

instance
  List-Eq : ∀ {A} {{_ : Eq A}} -> Eq (List A)
  List-Eq {A} = record { _≟_ = ≡-dec _≟_ }

  List-EqB : ∀ {A} {{_ : EqB A}} -> EqB (List A)
  List-EqB {A} = record { _≣_ = helper }
    where
      helper : (l l' : List A) -> Bool
      helper [] [] = true
      helper [] (x ∷ l') = false
      helper (x ∷ l) [] = false
      helper (x ∷ l) (x₁ ∷ l') = x ≣ x₁ ∧ helper l l'

  List-Monoid : ∀ {a} {A : Set a} -> Monoid (List A)
  List-Monoid = record { mzero = [] ; _+_ = _++_ }

  List-Traversable : ∀ {a} -> Traversable {a} (List {a})
  List-Traversable = record { sequence = helper }
    where
      helper : ∀ {a} {M : Set a → Set a} ⦃ _ : Monad M ⦄ {A : Set a} → List (M A) → M (List A)
      helper [] = return []
      helper (x ∷ xs) = do
        x' <- x
        xs' <- helper xs
        return (x' ∷ xs')

  List-Show : ∀ {a} {A : Set a} {{_ : Show A}} -> Show (List A)
  List-Show = record { show = showList show }
    where
      showList : ∀ {a} {A : Set a} -> (A -> String) -> List A -> String
      showList showA l = "[" + concat (intersperse "," (map showA l)) + "]"

  List-Monad : ∀ {a} -> Monad {a} List
  List-Monad = record { _>>=_ = λ l f -> concat (map f l) ; return = λ a -> Data.List.[ a ] }
