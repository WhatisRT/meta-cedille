module Theory.TermLike where

open import Prelude
open import Prelude.Nat
open import Theory.Names

import Data.Vec.Recursive
import Data.Vec.Recursive.Categorical
open import Data.Fin using (toℕ)

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
  CharT  : Const
  CharC  : Char → Const
  CharEq : Const
  MM MuM EpsilonM CatchM : Const

instance
  Const-EqB : EqB Const
  Const-EqB ._≣_ CharT     CharT      = true
  Const-EqB ._≣_ (CharC c) (CharC c') = c ≣ c'
  Const-EqB ._≣_ CharEq    CharEq     = true
  Const-EqB ._≣_ MM        MM         = true
  Const-EqB ._≣_ MuM       MuM        = true
  Const-EqB ._≣_ EpsilonM  EpsilonM   = true
  Const-EqB ._≣_ CatchM    CatchM     = true
  Const-EqB ._≣_ _ _                  = false

  Const-Show : Show Const
  Const-Show .show CharT     = "CharT"
  Const-Show .show (CharC c) = "'" + show c + "'"
  Const-Show .show CharEq    = "CharEq"
  Const-Show .show MM        = "MM"
  Const-Show .show MuM       = "MuM"
  Const-Show .show EpsilonM  = "EpsilonM"
  Const-Show .show CatchM    = "CatchM"

private variable
  A B C : Set
  c : Const

constArityF : Const → Fin 3
constArityF CharT     = 0F
constArityF (CharC x) = 0F
constArityF CharEq    = 2F
constArityF MM        = 1F
constArityF MuM       = 2F
constArityF EpsilonM  = 1F
constArityF CatchM    = 2F

constArity : Const → ℕ
constArity = toℕ ∘ constArityF

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

  modifyIndices : 𝕀 → T → T
  modifyIndices n = byUniformFold λ k x → BoundVar $ if x <𝕀 k then x else pred𝕀 (x +𝕀 n)

  weakenBy : 𝕀 → T → T
  weakenBy i = modifyIndices (suc𝕀 i)

  strengthen : T → T
  strengthen = modifyIndices 0

  -- substitute the first unbound variable in t with t'
  subst : T → T → T
  subst t t' = strengthen $ byUniformFold
    (λ k x → if k ≣ x then weakenBy (suc𝕀 k) t' else BoundVar x) t
