--------------------------------------------------------------------------------
-- This file provides the data structures and functions for the theory of
-- cedille core extended with the constructs for metaprogramming.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module CoreTheory where

import Agda.Builtin.Nat using (_+_; _-_; _==_)

import Data.Product

open import Class.Map
open import Class.Monad.Except
open import Data.HSTrie
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.String using (toList; fromList)
open import Data.Word using (Word64; toℕ; fromℕ)
open import Data.Word64.Exts
open import Monads.Except

open import Prelude

open import Theory.PrimMeta public

private
  variable
    A B C : Set
    M : Set → Set

data Sort : Set where
  ⋆ : Sort
  □ : Sort

instance
  Sort-Show : Show Sort
  Sort-Show = record { show = helper }
    where
      helper : Sort → String
      helper ⋆ = "*"
      helper □ = "□"

  Sort-Eq : Eq Sort
  Sort-Eq = record { _≟_ = helper }
    where
      helper : (s s' : Sort) → Dec (s ≡ s')
      helper ⋆ ⋆ = yes refl
      helper ⋆ □ = no λ ()
      helper □ ⋆ = no λ ()
      helper □ □ = yes refl

  Sort-EqB = Eq→EqB {{Sort-Eq}}

GlobalName : Set
GlobalName = String

𝕀 : Set
𝕀 = Word64

instance
  𝕀-Eq : Eq 𝕀
  𝕀-Eq = record { _≟_ = Data.Word._≟_ }

  𝕀-EqB : EqB 𝕀
  𝕀-EqB = record { _≣_ = Agda.Builtin.Nat._==_ on toℕ }

  𝕀-Show : Show 𝕀
  𝕀-Show = record { show = show ∘ toℕ }

_<𝕀_ : 𝕀 → 𝕀 → Bool
x <𝕀 y = toℕ x <ᵇ toℕ y

_+𝕀_ : 𝕀 → 𝕀 → 𝕀
x +𝕀 y = fromℕ $ toℕ x + toℕ y

_-𝕀_ : 𝕀 → 𝕀 → 𝕀
_-𝕀_ = subWord

suc𝕀 : 𝕀 → 𝕀
suc𝕀 = _+𝕀 fromℕ 1

pred𝕀 : 𝕀 → 𝕀
pred𝕀 = _-𝕀 fromℕ 1

data Name : Set where
  Bound : 𝕀 → Name
  Free : GlobalName → Name

instance
  Name-Eq : Eq Name
  Name-Eq = record { _≟_ = helper }
    where
      helper : (n n' : Name) → Dec (n ≡ n')
      helper (Bound x) (Bound x₁) with x ≟ x₁
      ... | yes p rewrite p = yes refl
      ... | no ¬p = no λ { refl → ¬p refl }
      helper (Bound x) (Free x₁) = no λ ()
      helper (Free x) (Bound x₁) = no λ ()
      helper (Free x) (Free x₁) with x ≟ x₁
      ... | yes p rewrite p = yes refl
      ... | no ¬p = no λ { refl → ¬p refl }

  Name-EqB : EqB Name
  Name-EqB = Eq→EqB

  Name-Show : Show Name
  Name-Show = record { show = helper }
    where
      helper : Name → String
      helper (Bound x) = show x
      helper (Free x) = x

record TermLike (T : Set) : Set where
  infixr -1 _⟪$⟫_ -- same as $
  field
    Var : Name → T
    _⟪$⟫_ : T → T → T

  BoundVar : 𝕀 → T
  BoundVar = Var ∘ Bound

  FreeVar : GlobalName → T
  FreeVar = Var ∘ Free

open TermLike {{...}} public

showVar : List String → Name → String
showVar l (Bound x) with lookupMaybe (toℕ x) l
... | nothing = show x
... | just x₁ = if x₁ ≣ "_" then show x else x₁
showVar l (Free x) = x

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

data PureTerm : Set where
  Var-P : Name → PureTerm
  Sort-P : Sort → PureTerm
  Const-P : Const → PureTerm
  App-P : PureTerm → PureTerm → PureTerm
  Lam-P : String → PureTerm → PureTerm
  Pi-P : String → PureTerm → PureTerm → PureTerm
  All-P : String → PureTerm → PureTerm → PureTerm
  Iota-P : String → PureTerm → PureTerm → PureTerm
  Eq-P : PureTerm → PureTerm → PureTerm
  M-P : PureTerm → PureTerm
  Mu-P : PureTerm → PureTerm → PureTerm
  Epsilon-P : PureTerm → PureTerm
  Gamma-P : PureTerm → PureTerm → PureTerm
  Ev-P : (m : PrimMeta) → primMetaArgs PureTerm m → PureTerm
  Char-P : Char → PureTerm
  CharEq-P : PureTerm → PureTerm → PureTerm

instance
  PureTerm-TermLike : TermLike PureTerm
  PureTerm-TermLike = record { Var = Var-P ; _⟪$⟫_ = App-P }

  {-# TERMINATING #-}
  PureTerm-Show : Show PureTerm
  PureTerm-Show = record { show = helper [] }
    where
      helper : List String → PureTerm → String
      helper l (Var-P x) = showVar l x
      helper l (Sort-P x) = show x
      helper l (Const-P x) = show x
      helper l (App-P t t₁) = "[" + helper l t + " " + helper l t₁ + "]"
      helper l (Lam-P n t) = "λ " + n + " " + helper (n ∷ l) t
      helper l (Pi-P n t t₁) = "Π " + n + " " + helper (n ∷ l) t + " " + helper l t₁
      helper l (All-P n t t₁) = "∀ " + n + " " + helper (n ∷ l) t + " " + helper l t₁
      helper l (Iota-P n t t₁) = "ι " + n + " " + helper (n ∷ l) t + " " + helper l t₁
      helper l (Eq-P t t₁) = "= " + helper l t + " " + helper l t₁
      helper l (M-P t) = "M " + helper l t
      helper l (Mu-P t t₁) = "μ " + helper l t + " " + helper l t₁
      helper l (Epsilon-P t) = "ε " + helper l t
      helper l (Gamma-P t t₁) = "Γ " + helper l t + " " + helper l t₁
      helper l (Ev-P m args) = "ζ " + show m + " " + primMetaArgs-Show (helper l) args
      helper l (Char-P c) = "Char " + show c
      helper l (CharEq-P t t') = "CharEq " + show t + " " + show t'

private
  beqMonadHelper : {{_ : EqB A}} {{_ : Show A}} {{_ : Monad M}} {{_ : MonadExcept M String}}
                → A → A → String → M ⊤
  beqMonadHelper a a' s =
    if a ≣ a'
      then return tt
      else throwError (s + " " + show a + " isn't equal to name " + show a')

{-# TERMINATING #-}
pureTermBeq : {{_ : Monad M}} {{_ : MonadExcept M String}}
  → PureTerm → PureTerm → M ⊤
pureTermBeq (Var-P x) (Var-P x₁) = beqMonadHelper x x₁ "Name"
pureTermBeq (Sort-P x) (Sort-P x₁) = beqMonadHelper x x₁ "Sort"
pureTermBeq (Const-P x) (Const-P x₁) = beqMonadHelper x x₁ "Const"
pureTermBeq (App-P t t₁) (App-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Lam-P _ t) (Lam-P _ t₁) = pureTermBeq t t₁
pureTermBeq (Pi-P _ t t₁) (Pi-P _ x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (All-P _ t t₁) (All-P _ x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Iota-P _ t t₁) (Iota-P _ x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Eq-P t t₁) (Eq-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (M-P t) (M-P x) = pureTermBeq x t
pureTermBeq (Mu-P t t₁) (Mu-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Epsilon-P t) (Epsilon-P x) = pureTermBeq t x
pureTermBeq (Gamma-P t t₁) (Gamma-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Ev-P m t) (Ev-P m' x) with m ≟ m'
... | yes refl = void $ primMetaArgsSequence $ primMetaArgsZipWith pureTermBeq t x
... | no  _    = throwError $ show m + " and " + show m' + " aren't equal!"
pureTermBeq (Char-P c) (Char-P c') = beqMonadHelper c c' "Char"
pureTermBeq (CharEq-P t t₁) (CharEq-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
{-# CATCHALL #-}
pureTermBeq t t' =
  throwError $ "The terms " + show t + " and " + show t' + " aren't equal!"

data AnnTerm : Set where
  Var-A : Name → AnnTerm
  Sort-A : Sort → AnnTerm
  Const-A : Const → AnnTerm
  Pr1-A : AnnTerm → AnnTerm
  Pr2-A : AnnTerm → AnnTerm
  Beta-A : AnnTerm → AnnTerm → AnnTerm -- proves first arg eq, erase to second arg
  Delta-A : AnnTerm → AnnTerm → AnnTerm -- inhabits first arg if snd arg proves false
  Sigma-A : AnnTerm → AnnTerm
  App-A : AnnTerm → AnnTerm → AnnTerm
  AppE-A : AnnTerm → AnnTerm → AnnTerm
  Rho-A : AnnTerm → AnnTerm → AnnTerm → AnnTerm -- first arg is eq, rewrite the name in the third arg and inhabit with fourth arg
  All-A : String → AnnTerm → AnnTerm → AnnTerm
  Pi-A : String → AnnTerm → AnnTerm → AnnTerm
  Iota-A : String → AnnTerm → AnnTerm → AnnTerm
  Lam-A : String → AnnTerm → AnnTerm → AnnTerm
  LamE-A : String → AnnTerm → AnnTerm → AnnTerm
  Pair-A : AnnTerm → AnnTerm → AnnTerm → AnnTerm
  Phi-A : AnnTerm → AnnTerm → AnnTerm → AnnTerm
  -- there is a let binding here, which is probably unnecessary
  Eq-A : AnnTerm → AnnTerm → AnnTerm
  M-A : AnnTerm → AnnTerm
  Mu-A : AnnTerm → AnnTerm → AnnTerm
  Epsilon-A : AnnTerm → AnnTerm
  Gamma-A : AnnTerm → AnnTerm → AnnTerm
  Ev-A : (x : PrimMeta) → primMetaArgs AnnTerm x → AnnTerm
  Char-A : Char → AnnTerm
  CharEq-A : AnnTerm → AnnTerm → AnnTerm

instance
  AnnTerm-TermLike : TermLike AnnTerm
  AnnTerm-TermLike = record { Var = Var-A ; _⟪$⟫_ = App-A }

  {-# TERMINATING #-}
  AnnTerm-Show : Show AnnTerm
  AnnTerm-Show = record { show = helper [] }
    where
      helper : List String → AnnTerm → String
      helper l (Var-A x)        = showVar l x
      helper l (Sort-A x)       = show x
      helper l (Const-A x)      = show x
      helper l (Pr1-A t)        = "π1 " + helper l t
      helper l (Pr2-A t)        = "π2 " + helper l t
      helper l (Beta-A t t₁)    = "β " + helper l t + " " + helper l t₁
      helper l (Delta-A t t₁)   = "Delta-A" + helper l t + " " + helper l t₁
      helper l (Sigma-A t)      = "ς" + helper l t
      helper l (App-A t t₁)     = "[" + helper l t + " " + helper l t₁ + "]"
      helper l (AppE-A t t₁)    = "<" + helper l t + " " + helper l t₁ + ">"
      helper l (Rho-A t t₁ t₂)  = "ρ " + helper l t + " : " + helper l t₁ + " " + helper l t₂
      helper l (All-A n t t₁)   = "∀ " + n + " : " + helper l t + ". " + helper (n ∷ l) t₁
      helper l (Pi-A n t t₁)    = "Π " + n + " : " + helper l t + ". " + helper (n ∷ l) t₁
      helper l (Iota-A n t t₁)  = "ι " + n + " : " + helper l t + ". " + helper (n ∷ l) t₁
      helper l (Lam-A n t t₁)   = "λ " + n + " : " + helper l t + ". " + helper (n ∷ l) t₁
      helper l (LamE-A n t t₁)  = "Λ " + n + " : " + helper l t + ". " + helper (n ∷ l) t₁
      helper l (Pair-A t t₁ t₂) = "{" + helper l t + "," + helper l t₁ + " . " + helper l t₂ + "}"
      helper l (Phi-A t t₁ t₂)  = "φ " + helper l t + " " + helper l t₁ + " " + helper l t₂
      helper l (Eq-A t t₁)      = "(= " + helper l t + " " + helper l t₁ + ")"
      helper l (M-A t)          = "M " + helper l t
      helper l (Mu-A t t₁)      = "μ " + helper l t + " " + helper l t₁
      helper l (Epsilon-A t)    = "ε " + helper l t
      helper l (Gamma-A t t₁)   = "Γ " + helper l t + " " + helper l t₁
      helper l (Ev-A m args)    = "Ev " + show m + " " + primMetaArgs-Show (helper l) args
      helper l (Char-A c)       = "Char " + show c
      helper l (CharEq-A t t')  = "CharEq " + show t + " " + show t'

primMetaS : (m : PrimMeta) → primMetaArgs AnnTerm m
primMetaS EvalStmt      = FreeVar "init$stmt"
primMetaS ShellCmd      = (FreeVar "init$string" , FreeVar "init$stringList")
primMetaS CheckTerm     = (Sort-A ⋆ , FreeVar "init$term")
primMetaS Parse         = (FreeVar "init$string" , Sort-A ⋆ , FreeVar "init$string")
primMetaS Normalize     = FreeVar "init$term"
primMetaS HeadNormalize = FreeVar "init$term"

primMetaT : (m : PrimMeta) → primMetaArgs AnnTerm m → AnnTerm
primMetaT EvalStmt _        = FreeVar "init$metaResult"
primMetaT ShellCmd _        = FreeVar "init$string"
primMetaT CheckTerm (t , _) = t
primMetaT Parse (_ , t , _) = t
primMetaT Normalize _       = FreeVar "init$term"
primMetaT HeadNormalize _   = FreeVar "init$term"

data Def : Set where
  Let : AnnTerm → AnnTerm → Def
  Axiom : AnnTerm → Def

data EfficientDef : Set where
  EfficientLet : AnnTerm → PureTerm → AnnTerm → EfficientDef
  EfficientAxiom : AnnTerm → EfficientDef

toDef : EfficientDef → Def
toDef (EfficientLet x x₁ x₂)   = Let x x₂
toDef (EfficientAxiom x)       = Axiom x

getNorm : EfficientDef → Maybe PureTerm
getNorm (EfficientLet x x₁ x₂) = return x₁
getNorm (EfficientAxiom x)     = nothing

instance
  Def-Show : Show Def
  Def-Show = record { show = helper }
    where
      helper : Def → String
      helper (Let x x₁) = " := " + show x + " : " + show x₁
      helper (Axiom x) = " : " + show x

typeOfDef : Def → AnnTerm
typeOfDef (Let _ x) = x
typeOfDef (Axiom x) = x

{-# TERMINATING #-}
modifyIndicesPure : 𝕀 → PureTerm → PureTerm
modifyIndicesPure = helper $ fromℕ 0
  where
    helper : 𝕀 → 𝕀 → PureTerm → PureTerm
    helper k n v@(Var-P (Bound x)) = if x <𝕀 k then v else BoundVar (pred𝕀 (x +𝕀 n))
    helper k n v@(Var-P (Free x))  = v
    helper k n v@(Sort-P x)        = v
    helper k n v@(Const-P x)       = v
    helper k n (App-P t t₁)        = App-P (helper k n t) (helper k n t₁)
    helper k n (Lam-P x t)         = Lam-P x (helper (suc𝕀 k) n t)
    helper k n (Pi-P x t t₁)       = Pi-P x (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (All-P x t t₁)      = All-P x (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Iota-P x t t₁)     = Iota-P x (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Eq-P t t₁)         = Eq-P (helper k n t) (helper k n t₁)
    helper k n (M-P t)             = M-P (helper k n t)
    helper k n (Mu-P t t₁)         = Mu-P (helper k n t) (helper k n t₁)
    helper k n (Epsilon-P t)       = Epsilon-P (helper k n t)
    helper k n (Gamma-P t t₁)      = Gamma-P (helper k n t) (helper k n t₁)
    helper k n (Ev-P m args)       = Ev-P m (mapPrimMetaArgs (helper k n) args)
    helper k n (Char-P c)          = Char-P c
    helper k n (CharEq-P t t')     = CharEq-P (helper k n t) (helper k n t')

incrementIndicesPureBy : 𝕀 → PureTerm → PureTerm
incrementIndicesPureBy i = modifyIndicesPure (suc𝕀 i)

decrementIndicesPure : PureTerm → PureTerm
decrementIndicesPure = modifyIndicesPure (fromℕ 0)

{-# TERMINATING #-}
modifyIndices : 𝕀 → AnnTerm → AnnTerm
modifyIndices = helper (fromℕ 0)
  where
    helper : 𝕀 → 𝕀 → AnnTerm → AnnTerm
    helper k n v@(Var-A (Bound x)) = if x <𝕀 k then v else BoundVar (pred𝕀 (x +𝕀 n))
    helper k n v@(Var-A (Free x)) = v
    helper k n (Sort-A x) = Sort-A x
    helper k n (Const-A x) = Const-A x
    helper k n (Pr1-A t) = Pr1-A $ helper k n t
    helper k n (Pr2-A t) = Pr2-A $ helper k n t
    helper k n (Beta-A t t₁) = Beta-A (helper k n t) (helper k n t₁)
    helper k n (Delta-A t t₁) = Delta-A (helper k n t) (helper k n t₁)
    helper k n (Sigma-A t) = Sigma-A (helper k n t)
    helper k n (App-A t t₁) = App-A (helper k n t) (helper k n t₁)
    helper k n (AppE-A t t₁) = AppE-A (helper k n t) (helper k n t₁)
    helper k n (Rho-A t t₁ t₂) = Rho-A (helper k n t) (helper (suc𝕀 k) n t₁) (helper k n t₂)
    helper k n (All-A x t t₁) = All-A x (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Pi-A x t t₁) = Pi-A x (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Iota-A x t t₁) = Iota-A x (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Lam-A x t t₁) = Lam-A x (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (LamE-A x t t₁) = LamE-A x (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Pair-A t t₁ t₂) = Pair-A (helper k n t) (helper k n t₁) (helper (suc𝕀 k) n t₂)
    helper k n (Phi-A t t₁ t₂) = Phi-A (helper k n t) (helper k n t₁) (helper k n t₂)
    helper k n (Eq-A t t₁) = Eq-A (helper k n t) (helper k n t₁)
    helper k n (M-A t) = M-A (helper k n t)
    helper k n (Mu-A t t₁) = Mu-A (helper k n t) (helper k n t₁)
    helper k n (Epsilon-A t) = Epsilon-A (helper k n t)
    helper k n (Gamma-A t t₁) = Gamma-A (helper k n t) (helper k n t₁)
    helper k n (Ev-A m args) = Ev-A m (mapPrimMetaArgs (helper k n) args)
    helper k n (Char-A c) = Char-A c
    helper k n (CharEq-A t t₁) = CharEq-A (helper k n t) (helper k n t₁)

incrementIndicesBy : 𝕀 → AnnTerm → AnnTerm
incrementIndicesBy i = modifyIndices (suc𝕀 i)

decrementIndices : AnnTerm → AnnTerm
decrementIndices = modifyIndices (fromℕ 0)

{-# TERMINATING #-}
checkFree : Name → PureTerm → Bool
checkFree = helper 0
  where
    helper : ℕ → Name → PureTerm → Bool
    helper k n (Var-P (Bound x)) = case n of λ
      { (Bound x₁) → x ≣ (fromℕ k +𝕀 x₁)
      ; (Free x₁) → false }
    helper k n (Var-P (Free x)) = case n of λ
      { (Bound x₁) → false
      ; (Free x₁) → x ≣ x₁ }
    helper k n (Sort-P x) = false
    helper k n (Const-P x) = false
    helper k n (App-P t t₁) = helper k n t ∧ helper k n t₁
    helper k n (Lam-P _ t) = helper (suc k) n t
    helper k n (Pi-P _ t t₁) = helper k n t ∧ helper (suc k) n t₁
    helper k n (All-P _ t t₁) = helper k n t ∧ helper (suc k) n t₁
    helper k n (Iota-P _ t t₁) = helper k n t ∧ helper (suc k) n t₁
    helper k n (Eq-P t t₁) = helper k n t ∧ helper k n t₁
    helper k n (M-P t) = helper k n t
    helper k n (Mu-P t t₁) = helper k n t ∧ helper k n t₁
    helper k n (Epsilon-P t) = helper k n t
    helper k n (Gamma-P t t₁) = helper k n t ∧ helper k n t₁
    helper k n (Ev-P m t) = primMetaArgsAnd $ mapPrimMetaArgs (helper k n) t
    helper k n (Char-P c) = false
    helper k n (CharEq-P t t₁) = helper k n t ∧ helper k n t₁

GlobalContext : Set
GlobalContext = HSTrie EfficientDef

emptyGlobalContext : GlobalContext
emptyGlobalContext = emptyMap

Context : Set
Context = GlobalContext × List AnnTerm

instance
  Context-Show : Show Context
  Context-Show = record { show = helper }
    where
      helper : Context → String
      helper (fst , snd) =
        (show $ length snd) + " local variables:" + show snd

globalToContext : GlobalContext → Context
globalToContext Γ = Γ , []

contextToGlobal : Context → GlobalContext
contextToGlobal (fst , snd) = fst

-- add variable to context, so that index 0 points to that variable
pushVar : AnnTerm → Context → Context
pushVar v (fst , snd) = fst , v ∷ snd

localContextLength : Context → ℕ
localContextLength (fst , snd) = length snd

efficientLookupInContext : Name → Context → Maybe EfficientDef
efficientLookupInContext (Bound x) (fst , snd) =
  EfficientAxiom ∘ incrementIndicesBy (suc𝕀 x) <$> lookupMaybe (toℕ x) snd
efficientLookupInContext (Free x) (fst , snd) = lookup x fst

lookupInContext : Name → Context → Maybe Def
lookupInContext n Γ = toDef <$> efficientLookupInContext n Γ

{-# TERMINATING #-}
validInContext : PureTerm → Context → Bool
validInContext = helper 0
  where
    -- instead of modifying the context here, we just count how many variables we would have added if we did
    helper : ℕ → PureTerm → Context → Bool
    helper k (Var-P (Bound x)) Γ = x <𝕀 fromℕ (localContextLength Γ + k)
    helper k (Var-P n@(Free x)) Γ = maybe (λ _ → true) false $ lookupInContext n Γ
    helper k (Sort-P x) Γ = true
    helper k (Const-P x) Γ = true
    helper k (App-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Lam-P _ t) Γ = helper (suc k) t Γ
    helper k (Pi-P _ t t₁) Γ = helper k t Γ ∧ helper (suc k) t₁ Γ
    helper k (All-P _ t t₁) Γ = helper k t Γ ∧ helper (suc k) t₁ Γ
    helper k (Iota-P _ t t₁) Γ = helper k t Γ ∧ helper (suc k) t₁ Γ
    helper k (Eq-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (M-P t) Γ = helper k t Γ
    helper k (Mu-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Epsilon-P t) Γ = helper k t Γ
    helper k (Gamma-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Ev-P m t) Γ = primMetaArgsAnd $ mapPrimMetaArgs (λ x → helper k x Γ) t
    helper k (Char-P c) Γ = true
    helper k (CharEq-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ

{-# TERMINATING #-}
Erase : AnnTerm → PureTerm
Erase (Var-A x)        = Var-P x
Erase (Sort-A x)       = Sort-P x
Erase (Const-A x)      = Const-P x
Erase (Pr1-A t)        = Erase t
Erase (Pr2-A t)        = Erase t
Erase (Beta-A t t₁)    = Erase t₁
Erase (Delta-A t t₁)   = Erase t₁
Erase (Sigma-A t)      = Erase t
Erase (App-A t t₁)     = App-P (Erase t) (Erase t₁)
Erase (AppE-A t t₁)    = Erase t
Erase (Rho-A t t₁ t₂)  = Erase t₂
Erase (All-A n t t₁)   = All-P n (Erase t) (Erase t₁)
Erase (Pi-A n t t₁)    = Pi-P n (Erase t) (Erase t₁)
Erase (Iota-A n t t₁)  = Iota-P n (Erase t) (Erase t₁)
Erase (Lam-A n t t₁)   = Lam-P n (Erase t₁)
Erase (LamE-A _ t t₁)  = decrementIndicesPure (Erase t₁)
Erase (Pair-A t t₁ t₂) = Erase t
Erase (Phi-A t t₁ t₂)  = Erase t₂
Erase (Eq-A x x₁)      = Eq-P (Erase x) (Erase x₁)
Erase (M-A t)          = M-P (Erase t)
Erase (Mu-A t t₁)      = Mu-P (Erase t) (Erase t₁)
Erase (Epsilon-A t)    = Epsilon-P (Erase t)
Erase (Gamma-A t t₁)   = Gamma-P (Erase t) (Erase t₁)
Erase (Ev-A m args)    = Ev-P m (mapPrimMetaArgs Erase args)
Erase (Char-A c)       = Char-P c
Erase (CharEq-A x x₁)  = CharEq-P (Erase x) (Erase x₁)

-- substitute the first unbound variable in t with t'
{-# TERMINATING #-}
subst : AnnTerm → AnnTerm → AnnTerm
subst t t' = decrementIndices $ substIndex t (fromℕ 0) t'
  where
    -- substitute the k-th unbound variable in t with t'
    substIndex : AnnTerm → 𝕀 → AnnTerm → AnnTerm
    substIndex v@(Var-A (Bound x)) k t' = if k ≣ x then incrementIndicesBy (suc𝕀 k) t' else v
    substIndex v@(Var-A (Free x)) k t' = v
    substIndex v@(Sort-A x) k t' = v
    substIndex v@(Const-A x) k t' = v
    substIndex (Pr1-A t) k t' = Pr1-A (substIndex t k t')
    substIndex (Pr2-A t) k t' = Pr2-A (substIndex t k t')
    substIndex (Beta-A t t₁) k t' = Beta-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (Delta-A t t₁) k t' = Delta-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (Sigma-A t) k t' = Sigma-A (substIndex t k t')
    substIndex (App-A t t₁) k t' = App-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (AppE-A t t₁) k t' = AppE-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (Rho-A t t₁ t₂) k t' = Rho-A (substIndex t k t') (substIndex t₁ k t') (substIndex t₂ k t')
    substIndex (All-A n t t₁) k t' = All-A n (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (Pi-A n t t₁) k t' = Pi-A n (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (Iota-A n t t₁) k t' = Iota-A n (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (Lam-A n t t₁) k t' = Lam-A n (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (LamE-A n t t₁) k t' = LamE-A n (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (Pair-A t t₁ t₂) k t' = Pair-A (substIndex t k t') (substIndex t₁ k t') (substIndex t₂ (suc𝕀 k) t')
    substIndex (Phi-A t t₁ t₂) k t' = Phi-A (substIndex t k t') (substIndex t₁ k t') (substIndex t₂ k t')
    substIndex (Eq-A t t₁) k t' = Eq-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (M-A t) k t' = M-A (substIndex t k t')
    substIndex (Mu-A t t₁) k t' = Mu-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (Epsilon-A t) k t' = Epsilon-A (substIndex t k t')
    substIndex (Gamma-A t t₁) k t' = Gamma-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (Ev-A m t) k t' = Ev-A m $ mapPrimMetaArgs (λ x → substIndex x k t') t
    substIndex (Char-A c) k t' = Char-A c
    substIndex (CharEq-A t t₁) k t' = CharEq-A (substIndex t k t') (substIndex t₁ k t')

-- substitute the first unbound variable in t with t'
{-# TERMINATING #-}
substPure : PureTerm → PureTerm → PureTerm
substPure t t' = decrementIndicesPure $ substIndexPure t (fromℕ 0) t'
  where
    -- substitute the k-th unbound variable in t with t'
    substIndexPure : PureTerm → 𝕀 → PureTerm → PureTerm
    substIndexPure v@(Var-P (Bound x)) k t' = if k ≣ x then incrementIndicesPureBy (suc𝕀 k) t' else v
    substIndexPure v@(Var-P (Free x)) k t' = v
    substIndexPure v@(Sort-P x) k t' = v
    substIndexPure v@(Const-P x) k t' = v
    substIndexPure (App-P t t₁) k t' = App-P (substIndexPure t k t') (substIndexPure t₁ k t')
    substIndexPure (Lam-P n t) k t' = Lam-P n (substIndexPure t (suc𝕀 k) t')
    substIndexPure (Pi-P n t t₁) k t' = Pi-P n (substIndexPure t k t') (substIndexPure t₁ (suc𝕀 k) t')
    substIndexPure (All-P n t t₁) k t' = All-P n (substIndexPure t k t') (substIndexPure t₁ (suc𝕀 k) t')
    substIndexPure (Iota-P n t t₁) k t' = Iota-P n (substIndexPure t k t') (substIndexPure t₁ (suc𝕀 k) t')
    substIndexPure (Eq-P t t₁) k t' = Eq-P (substIndexPure t k t') (substIndexPure t₁ k t')
    substIndexPure (M-P t) k t' = M-P (substIndexPure t k t')
    substIndexPure (Mu-P t t₁) k t' = Mu-P (substIndexPure t k t') (substIndexPure t₁ k t')
    substIndexPure (Epsilon-P t) k t' = Epsilon-P (substIndexPure t k t')
    substIndexPure (Gamma-P t t₁) k t' = Gamma-P (substIndexPure t k t') (substIndexPure t₁ k t')
    substIndexPure (Ev-P m t) k t' = Ev-P m $ mapPrimMetaArgs (λ x → substIndexPure x k t') t
    substIndexPure (Char-P c) k t' = Char-P c
    substIndexPure (CharEq-P t t₁) k t' = CharEq-P (substIndexPure t k t') (substIndexPure t₁ k t')

stripBinder : AnnTerm → Maybe AnnTerm
stripBinder (All-A  _ t' t'') = just t''
stripBinder (Pi-A   _ t' t'') = just t''
stripBinder (Iota-A _ t' t'') = just t''
stripBinder (Lam-A  _ t' t'') = just t''
stripBinder (LamE-A _ t' t'') = just t''
{-# CATCHALL #-}
stripBinder t                 = nothing

-- something in is head normal form, if its outermost constructor is not one of the following: Var-A (if the lookup fails), App-A, AppE-A
{-# TERMINATING #-}
hnfNorm : Context → AnnTerm → AnnTerm
hnfNorm Γ v@(Var-A x) with lookupInContext x Γ
... | just (Let x₁ x₂)  = hnfNorm Γ x₁
... | just (Axiom x₁)   = v -- we cannot reduce axioms
... | nothing           = v -- in case the lookup fails, we cannot reduce
hnfNorm Γ (App-A t t₁)  = maybe (λ t' → hnfNorm Γ $ subst t' t₁) (t ⟪$⟫ t₁) $ stripBinder (hnfNorm Γ t)
hnfNorm Γ (AppE-A t t₁) = maybe (λ t' → hnfNorm Γ $ subst t' t₁) (t ⟪$⟫ t₁) $ stripBinder (hnfNorm Γ t)
{-# CATCHALL #-}
hnfNorm Γ v             = v

stripBinderPure : PureTerm → Maybe PureTerm
stripBinderPure (Lam-P  _ t')     = just t'
stripBinderPure (Pi-P   _ t' t'') = just t''
stripBinderPure (All-P  _ t' t'') = just t''
stripBinderPure (Iota-P _ t' t'') = just t''
{-# CATCHALL #-}
stripBinderPure _                 = nothing

hnfNormPure : Context → PureTerm → PureTerm
normalizePure : Context → PureTerm → PureTerm

{-# NON_TERMINATING #-}
hnfNormPure Γ v@(Var-P x)       = case lookupInContext x Γ of λ where
  (just (Let x₁ x₂)) → hnfNormPure Γ $ Erase x₁
  (just (Axiom x₁))  → v -- we cannot reduce axioms
  nothing            → v -- in case the lookup fails, we cannot reduce
hnfNormPure Γ v@(App-P t t₁)    = case stripBinderPure (hnfNormPure Γ t) of λ where
  (just t') → hnfNormPure Γ $ substPure t' t₁
  nothing   → v
hnfNormPure Γ v@(CharEq-P t t₁) = normalizePure Γ v
{-# CATCHALL #-}
hnfNormPure Γ v                 = v

{-# NON_TERMINATING #-}
normalizePure Γ (Var-P x) with efficientLookupInContext x Γ
normalizePure Γ (Var-P x) | just (EfficientLet x₁ x₂ x₃) = x₂
normalizePure Γ v@(Var-P x) | just (EfficientAxiom x₁) = v -- we cannot reduce axioms
normalizePure Γ v@(Var-P x) | nothing = v -- in case the lookup fails, we cannot reduce
normalizePure Γ v@(Sort-P x) = v
normalizePure Γ v@(Const-P x) = v
normalizePure Γ (App-P t t₁) = case hnfNormPure Γ t of λ t' →
  case stripBinderPure t' of λ
    { (just t'') → normalizePure Γ (substPure t'' t₁)
    ; nothing → normalizePure Γ t ⟪$⟫ normalizePure Γ t₁ }
normalizePure Γ (Lam-P n t) = case normalizePure Γ t of λ
  { t''@(App-P t' (Var-P (Bound i))) → if i ≣ (fromℕ 0) ∧ validInContext t' Γ then decrementIndicesPure t' else Lam-P n t'' -- eta reduce here
  ; t'' → Lam-P n t'' }
normalizePure Γ (Pi-P n t t₁) = Pi-P n (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (All-P n t t₁) = All-P n (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Iota-P n t t₁) = Iota-P n (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Eq-P t t₁) = Eq-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (M-P t) = M-P (normalizePure Γ t)
normalizePure Γ (Mu-P t t₁) = Mu-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Epsilon-P t) = Epsilon-P (normalizePure Γ t)
normalizePure Γ (Gamma-P t t₁) = Gamma-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Ev-P m args) = Ev-P m (mapPrimMetaArgs (normalizePure Γ) args)
normalizePure Γ (Char-P c) = (Char-P c)
normalizePure Γ (CharEq-P t t₁) with normalizePure Γ t | normalizePure Γ t₁
... | (Char-P c) | (Char-P c') = normalizePure Γ $ if c ≣ c' then FreeVar "true" else (FreeVar "false")
{-# CATCHALL #-}
... | x | x₁ = CharEq-P x x₁

{-# TERMINATING #-}
findOutermostConstructor : PureTerm → PureTerm × List PureTerm
findOutermostConstructor t = outermostApp $ stripBinders t
  where
    stripBinders : PureTerm → PureTerm
    stripBinders t with stripBinderPure t
    stripBinders t | just x = stripBinders x
    stripBinders t | nothing = t

    outermostApp : PureTerm → PureTerm × List PureTerm
    outermostApp (App-P t t₁) = Data.Product.map id (t₁ ∷_) $ outermostApp t
    {-# CATCHALL #-}
    outermostApp t = t , []

insertInGlobalContext : GlobalName → Def → GlobalContext → String ⊎ GlobalContext
insertInGlobalContext n d Γ =
  if is-just $ lookup n Γ
    then inj₁ ("The name " + n + " is already defined!")
    else (inj₂ $ insert n (toEfficientDef d Γ) Γ)
  where
    toEfficientDef : Def → GlobalContext → EfficientDef
    toEfficientDef (Let x x₁) Γ = EfficientLet x (normalizePure (globalToContext Γ) $ Erase x) x₁
    toEfficientDef (Axiom x) Γ = EfficientAxiom x

module CheckEquality {{_ : Monad M}} {{_ : MonadExcept M String}} (Γ : Context) where

  compareNames : PureTerm → PureTerm → M ⊤
  compareNames (Var-P x) (Var-P x₁) =
    if x ≣ x₁
      then return tt
      else throwError "Names not equal! If you see this message, this is a bug!"
  {-# CATCHALL #-}
  compareNames _ _ = throwError "Terms are not names! If you see this message, this is a bug!"

  {-# NON_TERMINATING #-}
  checkβηPure : PureTerm → PureTerm → M ⊤
  checkβηPure t t' =
    tryElse (compareNames t t') $
    compareHnfs (hnfNormPure Γ t) (hnfNormPure Γ t')
    -- tryElse (compareHnfs (hnfNormPure Γ t) (hnfNormPure Γ t')) $
    -- pureTermBeq t t'
    where
      hnfError : PureTerm → PureTerm → M ⊤
      hnfError t t' =
        throwError $ "The terms " + show t + " and " + show t' + " aren't equal!"

      compareHnfs : PureTerm → PureTerm → M ⊤
      compareHnfs (Var-P x) (Var-P x₁) = beqMonadHelper x x₁ "Name"
      compareHnfs (Sort-P x) (Sort-P x₁) = beqMonadHelper x x₁ "Sort"
      compareHnfs (Const-P x) (Const-P x₁) = beqMonadHelper x x₁ "Const"
      compareHnfs (App-P t t₁) (App-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Lam-P _ t) (Lam-P _ t₁) = checkβηPure t t₁
      compareHnfs (Pi-P _ t t₁) (Pi-P _ x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (All-P _ t t₁) (All-P _ x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Iota-P _ t t₁) (Iota-P _ x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Eq-P t t₁) (Eq-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (M-P t) (M-P x) = checkβηPure x t
      compareHnfs (Mu-P t t₁) (Mu-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Epsilon-P t) (Epsilon-P x) = checkβηPure t x
      compareHnfs (Gamma-P t t₁) (Gamma-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs t@(Ev-P m x) t'@(Ev-P m' x') with m ≟ m'
      ... | yes refl = void $ primMetaArgsSequence $ primMetaArgsZipWith checkβηPure x x'
      ... | no  _    = hnfError t t'
      compareHnfs (Char-P c) (Char-P c') = beqMonadHelper c c' "Char"
      compareHnfs (CharEq-P t t₁) (CharEq-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Lam-P _ t) t₁ = case normalizePure Γ t of λ
        { t''@(App-P t' (Var-P (Bound i))) →
          if i ≣ (fromℕ 0) ∧ validInContext t' Γ then (compareHnfs (decrementIndicesPure t') t₁) else hnfError t'' t₁
        ; t'' → hnfError t'' t₁ }
      compareHnfs t (Lam-P _ t₁) = case normalizePure Γ t₁ of λ
        { t''@(App-P t' (Var-P (Bound i))) →
          if i ≣ (fromℕ 0) ∧ validInContext t' Γ then (compareHnfs t (decrementIndicesPure t')) else hnfError t t''
        ; t'' → hnfError t t'' }
      {-# CATCHALL #-}
      compareHnfs t t' = hnfError t t'

  checkβη : AnnTerm → AnnTerm → M ⊤
  checkβη t t' = checkβηPure (Erase t) (Erase t')

open CheckEquality public

{-# TERMINATING #-}
synthType synthType' :
  {{_ : Monad M}} {{_ : MonadExcept M String}} → Context → AnnTerm → M AnnTerm

synthType Γ t =
  appendIfError (synthType' Γ t) $
    "\n\nWhile synthesizing type for " + shortenString 1000 (show t) + " in context:\n" + show {{Context-Show}} Γ

synthType' Γ (Var-A x) =
  maybeToError
    (typeOfDef <$> lookupInContext x Γ)
    ("Lookup failed: " + show x + " in context " + show {{Context-Show}} Γ)
synthType' Γ (Sort-A ⋆) = return $ Sort-A □
synthType' Γ (Sort-A □) = throwError "Cannot synthesize type for the superkind"

synthType' Γ (Const-A CharT) = return $ Sort-A ⋆

synthType' Γ (Pr1-A t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Iota-A _ u u₁) → return u
    ; _ → throwError "Term does not normalize to an iota term" }

synthType' Γ (Pr2-A t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Iota-A _ u u₁) → return $ subst u₁ (Pr1-A t)
    ; _ → throwError "Term does not normalize to an iota term" }

synthType' Γ (Beta-A t t₁) = do
  T ← synthType Γ (Eq-A t t)
  case (hnfNorm Γ T) of λ
    { (Sort-A ⋆) → return $ Eq-A t t
    ; _ → throwError "Equality type does not have the right type. Is this a bug?" }

synthType' Γ (Delta-A t t₁) = do
  T ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (Eq-A u u₁) → do
      catchError
        (pureTermBeq (normalizePure Γ $ Erase u) (Lam-P "" $ Lam-P "" $ BoundVar $ fromℕ 1) >>
         pureTermBeq (normalizePure Γ $ Erase u₁) (Lam-P "" $ Lam-P "" $ BoundVar $ fromℕ 0))
        (λ e → throwError $
          "This equality cannot be used for the delta term: " + show u
          + " = " + show u₁ + "\nError: " + e)
      return t
    ; _ → throwError "The second argument of a delta needs to be of an eq type" }

synthType' Γ (Sigma-A t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Eq-A u u₁) → return $ Eq-A u₁ u
    ; _ → throwError "Sigma needs an inhabitant of an eq type as argument" }

synthType' Γ (App-A t t₁) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (Pi-A _ u u₁) → do
      catchError
        (checkβη Γ T₁ u)
        (λ e → throwError ("Type mismatch in application, the type of " + show t₁
          + " : " + show T₁ +  " is not βη-equivalent to " + show u + "\nError: " + e))
      return $ subst u₁ t₁
    ; v → throwError $
      "The left term in an application needs to have a pi type, while it has type " + show v }

synthType' Γ (AppE-A t t₁) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (All-A _ u u₁) → do
      catchError (checkβη Γ u T₁)
        (λ e → throwError
          ("Type mismatch in erased application, the following types are not βη-equivalent:\n"
            + show u + "\n" + show T₁ + "\nError:\n" + e))
      return $ subst u₁ t₁
    ; v → throwError $
      "The left term in an erased application needs to have a forall type, while it has type "
        + show v + "\nTest: " + show T }

synthType' Γ (Rho-A t t₁ t₂) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₂
  case (hnfNorm Γ T) of λ
    { (Eq-A u u₁) → do
      catchError (checkβη Γ (subst t₁ u₁) T₁)
        (λ e → throwError $ "Type mismatch in rho: " + show (subst t₁ u₁)
          + " should be βη-equivalent to the synthesized type of " + show t₂ + " : "
          + show T₁ + "\nError:\n" + e)
      return $ subst t₁ u
    ; _ → throwError "The type of the first argument of a rho needs to be an equality" }

synthType' Γ (All-A _ t t₁) = do
  u ← synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-A s) → do
      let Γ' = pushVar t Γ
      u₁ ← synthType Γ' t₁
      case (hnfNorm Γ' u₁) of λ
        { (Sort-A ⋆) → return $ Sort-A ⋆
        ; v → throwError $
          "The type family in forall should have type star, while it has type "
          + show v + " (" + show t₁ + ")\nContext: " + show {{Context-Show}} Γ' }
    ; _ → throwError "The type of the parameter type in forall should be star or square" }

synthType' Γ (Pi-A _ t t₁) = do
  u ← synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-A s) → do
      let Γ' = pushVar t Γ
      u₁ ← synthType Γ' t₁
      case (hnfNorm Γ u₁) of λ
        { (Sort-A s') → return $ Sort-A s'
        ; v → throwError $
          "The type family in pi should have type star or square, while it has type " + show v }
    ; _ → throwError "The type of the parameter type in pi should be star or square" }

synthType' Γ (Iota-A _ t t₁) = do
  u ← synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-A ⋆) → do
      let Γ' = pushVar t Γ
      u₁ ← synthType Γ' t₁
      case (hnfNorm Γ' u₁) of λ
        { (Sort-A ⋆) → return $ Sort-A ⋆
        ; _ → throwError "The type family in iota should have type star"}
    ; _ → throwError "The type of the parameter type in iota should be star" }

synthType' Γ (Lam-A n t t₁) = do
  synthType Γ t
  u ← synthType (pushVar t Γ) t₁
  return (Pi-A n t u)

synthType' Γ (LamE-A n t t₁) =
  if checkFree (Bound (fromℕ 0)) (Erase t₁)
    then throwError "Erased arguments cannot appear bound in a term"
    else do
      synthType Γ t
      u ← synthType (pushVar t Γ) t₁
      return $ All-A n t u

synthType' Γ (Pair-A t t₁ t₂) = do
  catchError (checkβη Γ t t₁)
    (λ e → throwError $
      "The terms in dependent intersection introduction have to be βη-equivalent. They normalize to:\n"
        + show (normalizePure Γ $ Erase t) + "\n"
        + show (normalizePure Γ $ Erase t₁) + "\nError:\n" + e)
  u ← synthType Γ t
  u₁ ← synthType Γ t₁
  catchError
    (checkβη Γ (subst t₂ t) u₁)
    (λ e → throwError
      ("Type mismatch in the second argument of the dependent intersection: "
        + show (subst t₂ t) + " should be βη-equivalent to the synthesized type "
        + show u₁ + "\n" + e))
  let res = Iota-A "" u t₂
  u₂ ← synthType Γ res
  case (hnfNorm Γ u₂) of λ
    { (Sort-A ⋆) → return res
    ; _ → throwError
      "The resulting iota type of the dependent intersection doesn't have type star. Is this a Bug?" }

synthType' Γ (Phi-A t t₁ t₂) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Eq-A u u₁) → do
      catchError
        (checkβη Γ t₁ u >> checkβη Γ t₂ u₁)
        (λ e → throwError $
          "The arguments to phi are not equivalent to the sides of the equality. Error:\n" + e)
      synthType Γ t₁
    ; _ → throwError "The first argument to phi should be of an equality type" }

synthType' Γ (Eq-A x x₁) =
  if validInContext (Erase x) Γ
    then if validInContext (Erase x₁) Γ
      then return $ Sort-A ⋆
      else throwError
        ("The right term in the equality type needs to be valid in the context: " + show x₁)
    else throwError
      ("The left term in the equality type needs to be valid in the context: " + show x)

synthType' Γ (M-A t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Sort-A ∗) → return $ Sort-A ∗
    ; _ → throwError "The term M is applied to should have type ∗"}

synthType' Γ (Mu-A t t₁) = do
  T ← synthType Γ t
  T' ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (M-A u) →
      case (hnfNorm Γ T') of λ
        { (Pi-A _ v v₁) → do
          T'' ← if checkFree (Bound $ fromℕ 0) (Erase v₁)
            then throwError ("Index 0 is not allowed to appear in " + show v₁)
            else synthType (pushVar v Γ) v₁
          case (hnfNorm Γ T'') of λ
            { (Sort-A ∗) →
              case (hnfNorm Γ v₁) of λ
                { (M-A v₂) →
                  appendIfError
                    (checkβη Γ u v)
                    "The types in μ need to be compatible" >> return (M-A $ decrementIndices v₂)
                ; _ → throwError
                  "The second term in a μ needs to have a Pi type that maps to 'M t' for some 't'" }
            ; _ → throwError "The second term in a μ needs to have a non-dependent Pi type" }
        ; _ → throwError "The second term in a μ needs to have a Pi type" }
    ; _ → throwError "The first term in a μ needs to have type 'M t' for some 't'" }

synthType' Γ (Epsilon-A t) = do
  T ← synthType Γ t
  return $ M-A T

synthType' Γ (Ev-A m t) = do
  T ← traversePrimMetaArgs (synthType Γ) t
  appendIfError
    (primMetaArgsSequence $ primMetaArgsZipWith (checkβη Γ) T $ primMetaS m)
    ("The arguments for primitive " + show m + " have incorrect types!")
  return $ M-A $ primMetaT m t

synthType' Γ (Gamma-A t t₁) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (M-A u) → do
      appendIfError (checkβη Γ T₁ (Pi-A "" (FreeVar "init$err") (incrementIndicesBy (fromℕ 1) $ M-A u)))
        ("The second term supplied to CatchErr has type " + show T₁ +
         ", while it should have type 'init$err → M " + show u)
      return $ M-A u
    ; _ → throwError "The first term in CatchErr needs to have type 'M t' for some 't'" }

synthType' Γ (Char-A c) = return (Const-A CharT)
synthType' Γ (CharEq-A t t') = do
  T ← synthType Γ t
  T' ← synthType Γ t'
  case (hnfNorm Γ T) of λ
    { (Const-A CharT) → case (hnfNorm Γ T') of λ
      { (Const-A CharT) → return $ FreeVar "Bool"
      ; _ → throwError "The second term in CharEq needs to have type Char" }
    ; _ → throwError "The first term in CharEq needs to have type Char" }
