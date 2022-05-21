module Theory.TermLike where

open import Prelude
open import Theory.Names

data Sort : Set where
  Ast : Sort
  Sq : Sort

instance
  Sort-Show : Show Sort
  Sort-Show = record { show = helper }
    where
      helper : Sort → String
      helper Ast = "*"
      helper Sq = "□"

  Sort-Eq : Eq Sort
  Sort-Eq = record { _≟_ = helper }
    where
      helper : (s s' : Sort) → Dec (s ≡ s')
      helper Ast Ast = yes refl
      helper Ast Sq = no λ ()
      helper Sq Ast = no λ ()
      helper Sq Sq = yes refl

  Sort-EqB = Eq→EqB {{Sort-Eq}}

data Const : Set where
  CharT : Const

instance
  Const-Eq : Eq Const
  Const-Eq = record { _≟_ = helper }
    where
      helper : (c c' : Const) → Dec (c ≡ c')
      helper CharT CharT = yes refl

  Const-EqB : EqB Const
  Const-EqB = Eq→EqB

  Const-Show : Show Const
  Const-Show = record { show = helper }
    where
      helper : Const → String
      helper CharT = "CharT"

record TermLike (T : Set) : Set where
  infixl -1 _⟪$⟫_ -- same as $ but on the left
  field
    Var : Name → T
    SortC : Sort → T
    _⟪$⟫_ : T → T → T

  BoundVar : 𝕀 → T
  BoundVar = Var ∘ Bound

  FreeVar : GlobalName → T
  FreeVar = Var ∘ Free

  ⋆ : T
  ⋆ = SortC Ast

  □ : T
  □ = SortC Sq

open TermLike {{...}} public
