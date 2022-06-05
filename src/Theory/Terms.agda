--------------------------------------------------------------------------------
-- Annotated and pure trems and basic term-related functions
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Theory.Terms where

open import Prelude
open import Prelude.Nat

open import Theory.Names public
open import Theory.TermLike public
open import Theory.PrimMeta public

private variable b : Bool

-- the bool decides whether to have the NBE constructors
data PureTerm : @0 Bool → Set where
  Var-P     : Name → PureTerm b
  FDB-P     : 𝕀 → PureTerm true
  Sort-P    : Sort → PureTerm b
  Const-P   : Const → PureTerm b
  App-P     : PureTerm b → PureTerm b → PureTerm b
  Lam-P     : String → PureTerm b → PureTerm b
  Cont-P    : String → List (String × Maybe (PureTerm true)) → PureTerm true → PureTerm true
  Pi-P      : String → PureTerm b → PureTerm b → PureTerm b
  All-P     : String → PureTerm b → PureTerm b → PureTerm b
  Iota-P    : String → PureTerm b → PureTerm b → PureTerm b
  Eq-P      : PureTerm b → PureTerm b → PureTerm b
  M-P       : PureTerm b → PureTerm b
  Mu-P      : PureTerm b → PureTerm b → PureTerm b
  Epsilon-P : PureTerm b → PureTerm b
  Gamma-P   : PureTerm b → PureTerm b → PureTerm b
  Ev-P      : (m : PrimMeta) → primMetaArgs (PureTerm b) m → PureTerm b
  Char-P    : Char → PureTerm b
  CharEq-P  : PureTerm b → PureTerm b → PureTerm b

instance
  {-# TERMINATING #-}
  PureTerm-TermLike : TermLike (PureTerm b)
  PureTerm-TermLike .Var             = Var-P
  PureTerm-TermLike .SortC           = Sort-P
  PureTerm-TermLike ._⟪$⟫_           = App-P
  PureTerm-TermLike {b} .byUniformFold f = helper 0
    where
      helper : 𝕀 → PureTerm b → PureTerm b
      helper k (Var-P (Bound x))  = f k x
      helper k v@(FDB-P _)        = v
      helper k v@(Var-P (Free _)) = v
      helper k v@(Sort-P x)       = v
      helper k v@(Const-P x)      = v
      helper k (App-P t t₁)       = App-P (helper k t) (helper k t₁)
      helper k (Lam-P x t)        = Lam-P x (helper (suc𝕀 k) t)
      helper k v@(Cont-P _ _ _)   = v
      helper k (Pi-P x t t₁)      = Pi-P x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (All-P x t t₁)     = All-P x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Iota-P x t t₁)    = Iota-P x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Eq-P t t₁)        = Eq-P (helper k t) (helper k t₁)
      helper k (M-P t)            = M-P (helper k t)
      helper k (Mu-P t t₁)        = Mu-P (helper k t) (helper k t₁)
      helper k (Epsilon-P t)      = Epsilon-P (helper k t)
      helper k (Gamma-P t t₁)     = Gamma-P (helper k t) (helper k t₁)
      helper k (Ev-P m args)      = Ev-P m (mapPrimMetaArgs (helper k) args)
      helper k (Char-P c)         = Char-P c
      helper k (CharEq-P t t')    = CharEq-P (helper k t) (helper k t')
  PureTerm-TermLike .stripBinder (All-P  _ t' t'') = just t''
  PureTerm-TermLike .stripBinder (Pi-P   _ t' t'') = just t''
  PureTerm-TermLike .stripBinder (Iota-P _ t' t'') = just t''
  PureTerm-TermLike .stripBinder (Lam-P  _ t')     = just t'
  PureTerm-TermLike .stripBinder _                 = nothing

  {-# TERMINATING #-}
  PureTerm-Show : Show (PureTerm b)
  PureTerm-Show = record { show = helper [] }
    where
      helper : List String → PureTerm b → String
      helper l (Var-P x)       = showVar l x
      helper l (FDB-P x)       = "FDB" <+> show x
      helper l (Sort-P x)      = show x
      helper l (Const-P x)     = show x
      helper l (App-P t t₁)    = "[" + helper l t <+> helper l t₁ + "]"
      helper l (Lam-P n t)     = "λ" <+> n + "." <+> helper (n ∷ l) t
      helper l (Cont-P n _ t)  = "Cont" <+> n + "." <+> helper (n ∷ l) t
      helper l (Pi-P n t t₁)   = "Π" <+> n <+> ":" <+> helper l t + "." <+> helper (n ∷ l) t₁
      helper l (All-P n t t₁)  = "∀" <+> n <+> ":" <+> helper l t + "." <+> helper (n ∷ l) t₁
      helper l (Iota-P n t t₁) = "ι" <+> n <+> ":" <+> helper l t + "." <+> helper (n ∷ l) t₁
      helper l (Eq-P t t₁)     = "=" <+> helper l t <+> helper l t₁
      helper l (M-P t)         = "M" <+> helper l t
      helper l (Mu-P t t₁)     = "μ" <+> helper l t <+> helper l t₁
      helper l (Epsilon-P t)   = "ε" <+> helper l t
      helper l (Gamma-P t t₁)  = "Γ" <+> helper l t <+> helper l t₁
      helper l (Ev-P m args)   = "ζ" <+> show m <+> primMetaArgs-Show (helper l) args
      helper l (Char-P c)      = "Char" <+> show c
      helper l (CharEq-P t t') = "CharEq" <+> show t <+> show t'

data AnnTerm : Set where
  Var-A     : Name → AnnTerm
  Sort-A    : Sort → AnnTerm
  Const-A   : Const → AnnTerm
  Pr1-A     : AnnTerm → AnnTerm
  Pr2-A     : AnnTerm → AnnTerm
  Beta-A    : AnnTerm → AnnTerm → AnnTerm -- proves first arg eq, erase to second arg
  Delta-A   : AnnTerm → AnnTerm → AnnTerm -- inhabits first arg if snd arg proves false
  Sigma-A   : AnnTerm → AnnTerm
  App-A     : AnnTerm → AnnTerm → AnnTerm
  AppE-A    : AnnTerm → AnnTerm → AnnTerm
  Rho-A     : AnnTerm → AnnTerm → AnnTerm → AnnTerm -- first arg is eq, rewrite the name in the third arg and inhabit with fourth arg
  All-A     : String → AnnTerm → AnnTerm → AnnTerm
  Pi-A      : String → AnnTerm → AnnTerm → AnnTerm
  Iota-A    : String → AnnTerm → AnnTerm → AnnTerm
  Lam-A     : String → AnnTerm → AnnTerm → AnnTerm
  LamE-A    : String → AnnTerm → AnnTerm → AnnTerm
  Pair-A    : AnnTerm → AnnTerm → AnnTerm → AnnTerm
  Phi-A     : AnnTerm → AnnTerm → AnnTerm → AnnTerm
  -- there is a let binding here, which is probably unnecessary
  Eq-A      : AnnTerm → AnnTerm → AnnTerm
  M-A       : AnnTerm → AnnTerm
  Mu-A      : AnnTerm → AnnTerm → AnnTerm
  Epsilon-A : AnnTerm → AnnTerm
  Gamma-A   : AnnTerm → AnnTerm → AnnTerm
  Ev-A      : (x : PrimMeta) → primMetaArgs AnnTerm x → AnnTerm
  Char-A    : Char → AnnTerm
  CharEq-A  : AnnTerm → AnnTerm → AnnTerm

instance
  {-# TERMINATING #-}
  AnnTerm-TermLike : TermLike AnnTerm
  AnnTerm-TermLike .Var             = Var-A
  AnnTerm-TermLike .SortC           = Sort-A
  AnnTerm-TermLike ._⟪$⟫_           = App-A
  AnnTerm-TermLike .byUniformFold f = helper 0
    where
      helper : 𝕀 → AnnTerm → AnnTerm
      helper k v@(Var-A (Bound x)) = f k x
      helper k v@(Var-A (Free _))  = v
      helper k v@(Sort-A x)        = v
      helper k v@(Const-A x)       = v
      helper k (Pr1-A t)           = Pr1-A $ helper k t
      helper k (Pr2-A t)           = Pr2-A $ helper k t
      helper k (Beta-A t t₁)       = Beta-A (helper k t) (helper k t₁)
      helper k (Delta-A t t₁)      = Delta-A (helper k t) (helper k t₁)
      helper k (Sigma-A t)         = Sigma-A (helper k t)
      helper k (App-A t t₁)        = App-A (helper k t) (helper k t₁)
      helper k (AppE-A t t₁)       = AppE-A (helper k t) (helper k t₁)
      helper k (Rho-A t t₁ t₂)     = Rho-A (helper k t) (helper (suc𝕀 k) t₁) (helper k t₂)
      helper k (All-A x t t₁)      = All-A x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Pi-A x t t₁)       = Pi-A x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Iota-A x t t₁)     = Iota-A x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Lam-A x t t₁)      = Lam-A x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (LamE-A x t t₁)     = LamE-A x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Pair-A t t₁ t₂)    = Pair-A (helper k t) (helper k t₁) (helper (suc𝕀 k) t₂)
      helper k (Phi-A t t₁ t₂)     = Phi-A (helper k t) (helper k t₁) (helper k t₂)
      helper k (Eq-A t t₁)         = Eq-A (helper k t) (helper k t₁)
      helper k (M-A t)             = M-A (helper k t)
      helper k (Mu-A t t₁)         = Mu-A (helper k t) (helper k t₁)
      helper k (Epsilon-A t)       = Epsilon-A (helper k t)
      helper k (Gamma-A t t₁)      = Gamma-A (helper k t) (helper k t₁)
      helper k (Ev-A m args)       = Ev-A m (mapPrimMetaArgs (helper k) args)
      helper k (Char-A c)          = Char-A c
      helper k (CharEq-A t t₁)     = CharEq-A (helper k t) (helper k t₁)
  AnnTerm-TermLike .stripBinder (All-A  _ t' t'') = just t''
  AnnTerm-TermLike .stripBinder (Pi-A   _ t' t'') = just t''
  AnnTerm-TermLike .stripBinder (Iota-A _ t' t'') = just t''
  AnnTerm-TermLike .stripBinder (Lam-A  _ t' t'') = just t''
  AnnTerm-TermLike .stripBinder (LamE-A _ t' t'') = just t''
  AnnTerm-TermLike .stripBinder _                 = nothing

  {-# TERMINATING #-}
  AnnTerm-Show : Show AnnTerm
  AnnTerm-Show = record { show = helper [] }
    where
      helper : List String → AnnTerm → String
      helper l (Var-A x)        = showVar l x
      helper l (Sort-A x)       = show x
      helper l (Const-A x)      = show x
      helper l (Pr1-A t)        = "π1" <+> helper l t
      helper l (Pr2-A t)        = "π2" <+> helper l t
      helper l (Beta-A t t₁)    = "β" <+> helper l t <+> helper l t₁
      helper l (Delta-A t t₁)   = "Delta-A" + helper l t <+> helper l t₁
      helper l (Sigma-A t)      = "ς" + helper l t
      helper l (App-A t t₁)     = "[" + helper l t <+> helper l t₁ + "]"
      helper l (AppE-A t t₁)    = "<" + helper l t <+> helper l t₁ + ">"
      helper l (Rho-A t t₁ t₂)  = "ρ" <+> helper l t <+> ":" <+> helper l t₁ <+> helper l t₂
      helper l (All-A n t t₁)   = "∀" <+> n <+> ":" <+> helper l t + "." <+> helper (n ∷ l) t₁
      helper l (Pi-A n t t₁)    = "Π" <+> n <+> ":" <+> helper l t + "." <+> helper (n ∷ l) t₁
      helper l (Iota-A n t t₁)  = "ι" <+> n <+> ":" <+> helper l t + "." <+> helper (n ∷ l) t₁
      helper l (Lam-A n t t₁)   = "λ" <+> n <+> ":" <+> helper l t + "." <+> helper (n ∷ l) t₁
      helper l (LamE-A n t t₁)  = "Λ" <+> n <+> ":" <+> helper l t + "." <+> helper (n ∷ l) t₁
      helper l (Pair-A t t₁ t₂) = "{" + helper l t + "," + helper l t₁ <+> "." <+> helper l t₂ + "}"
      helper l (Phi-A t t₁ t₂)  = "φ" <+> helper l t <+> helper l t₁ <+> helper l t₂
      helper l (Eq-A t t₁)      = "(=" <+> helper l t <+> helper l t₁ + ")"
      helper l (M-A t)          = "M" <+> helper l t
      helper l (Mu-A t t₁)      = "μ" <+> helper l t <+> helper l t₁
      helper l (Epsilon-A t)    = "ε" <+> helper l t
      helper l (Gamma-A t t₁)   = "Γ" <+> helper l t <+> helper l t₁
      helper l (Ev-A m args)    = "Ev" <+> show m <+> primMetaArgs-Show (helper l) args
      helper l (Char-A c)       = "Char" <+> show c
      helper l (CharEq-A t t')  = "CharEq" <+> show t <+> show t'

{-# TERMINATING #-}
Erase : AnnTerm → PureTerm b
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
Erase (LamE-A _ t t₁)  = strengthen (Erase t₁)
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
