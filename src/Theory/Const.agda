module Theory.Const where

open import Prelude
open import Prelude.Nat

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
  Fix : Const

instance
  Const-EqB : EqB Const
  Const-EqB ._≣_ CharT     CharT      = true
  Const-EqB ._≣_ (CharC c) (CharC c') = c ≣ c'
  Const-EqB ._≣_ CharEq    CharEq     = true
  Const-EqB ._≣_ MM        MM         = true
  Const-EqB ._≣_ MuM       MuM        = true
  Const-EqB ._≣_ EpsilonM  EpsilonM   = true
  Const-EqB ._≣_ CatchM    CatchM     = true
  Const-EqB ._≣_ Fix       Fix        = true
  Const-EqB ._≣_ _ _                  = false

  Const-Show : Show Const
  Const-Show .show CharT     = "CharT"
  Const-Show .show (CharC c) = "'" + show c + "'"
  Const-Show .show CharEq    = "CharEq"
  Const-Show .show MM        = "MM"
  Const-Show .show MuM       = "MuM"
  Const-Show .show EpsilonM  = "EpsilonM"
  Const-Show .show CatchM    = "CatchM"
  Const-Show .show Fix       = "Fix"

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
constArityF Fix       = 1F

constArity : Const → ℕ
constArity = toℕ ∘ constArityF
