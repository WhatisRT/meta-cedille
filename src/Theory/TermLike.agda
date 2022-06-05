module Theory.TermLike where

open import Prelude
open import Prelude.Nat
open import Theory.Names

data Sort : Set where
  Ast : Sort
  Sq  : Sort

instance
  Sort-Show : Show Sort
  Sort-Show .show Ast = "*"
  Sort-Show .show Sq  = "□"

  Sort-Eq : Eq Sort
  Sort-Eq ._≟_ Ast Ast = yes refl
  Sort-Eq ._≟_ Ast Sq  = no λ ()
  Sort-Eq ._≟_ Sq Ast  = no λ ()
  Sort-Eq ._≟_ Sq Sq   = yes refl

  Sort-EqB = Eq→EqB {{Sort-Eq}}

data Const : Set where
  CharT : Const

instance
  Const-Eq : Eq Const
  Const-Eq ._≟_ CharT CharT = yes refl

  Const-EqB : EqB Const
  Const-EqB = Eq→EqB

  Const-Show : Show Const
  Const-Show .show CharT = "CharT"

record TermLike (T : Set) : Set where
  infixl -1 _⟪$⟫_ -- same as $ but on the left
  field
    Var           : Name → T
    SortC         : Sort → T
    _⟪$⟫_         : T → T → T
    byUniformFold : (𝕀 → 𝕀 → T) → T → T
    stripBinder   : T → Maybe T

  BoundVar : 𝕀 → T
  BoundVar = Var ∘ Bound

  FreeVar : GlobalName → T
  FreeVar = Var ∘ Free

  ⋆ : T
  ⋆ = SortC Ast

  □ : T
  □ = SortC Sq

open TermLike ⦃...⦄ public

module _ {T : Set} ⦃ _ : TermLike T ⦄ where
  {-# TERMINATING #-}
  modifyIndices : 𝕀 → T → T
  modifyIndices n = byUniformFold λ k x → BoundVar $ if x <𝕀 k then x else pred𝕀 (x +𝕀 n)

  weakenBy : 𝕀 → T → T
  weakenBy i = modifyIndices (suc𝕀 i)

  strengthen : T → T
  strengthen = modifyIndices 0

  -- substitute the first unbound variable in t with t'
  {-# TERMINATING #-}
  subst : T → T → T
  subst t t' = strengthen $ byUniformFold
    (λ k x → if k ≣ x then weakenBy (suc𝕀 k) t' else BoundVar x) t

  evalCharEq : Char → Char → T
  evalCharEq c c' = FreeVar $ show (c ≣ c')
