--------------------------------------------------------------------------------
-- Annotated and pure trems and basic term-related functions
--------------------------------------------------------------------------------

module Theory.Terms where

open import Prelude
open import Prelude.Nat

open import Theory.Names public
open import Theory.TermLike
open import Theory.PrimMeta public

private variable a b : Bool

-- the second bool decides whether to have the NBE constructors
data Term : @0 Bool → @0 Bool → Set where
  Var-T   : Name → Term a b
  FDB     : 𝕀 → Term a true
  Sort-T  : Sort → Term a b
  Const-T : Const → Term a b
  App     : Term a b → Term a b → Term a b
  AppE    : Term true b → Term true b → Term true b
  Lam-P   : String → Term false b → Term false b
  Lam-A   : String → Term true b → Term true b → Term true b
  LamE    : String → Term true b → Term true b → Term true b
  Cont    : String → List (String × Maybe (Term a true)) → Term a true → Term a true
  Pi      : String → Term a b → Term a b → Term a b
  All     : String → Term a b → Term a b → Term a b
  Iota    : String → Term a b → Term a b → Term a b
  Eq-T    : Term a b → Term a b → Term a b
  M-T     : Term a b → Term a b
  Mu      : Term a b → Term a b → Term a b
  Epsilon : Term a b → Term a b
  Gamma   : Term a b → Term a b → Term a b
  Ev      : (m : PrimMeta) → primMetaArgs (Term a b) m → Term a b
  Char-T  : Char → Term a b
  CharEq  : Term a b → Term a b → Term a b
  Pr1     : Term true b → Term true b
  Pr2     : Term true b → Term true b
  Beta    : Term true b → Term true b → Term true b -- proves first arg eq, erase to second arg
  Delta   : Term true b → Term true b → Term true b -- inhabits first arg if snd arg proves false
  Sigma   : Term true b → Term true b
  Rho     : Term true b → Term true b → Term true b → Term true b -- first arg is eq, rewrite the name in the third arg and inhabit with fourth arg
  Pair    : Term true b → Term true b → Term true b → Term true b
  Phi     : Term true b → Term true b → Term true b → Term true b
  -- there is a let binding here, which is probably unnecessary

PureTerm : @0 Bool → Set
PureTerm = Term false

AnnTerm : Set
AnnTerm = Term true false

module _ where
  open TermLike

  {-# TERMINATING #-}
  Term-TermLike : TermLike (Term a b)
  Term-TermLike .Var             = Var-T
  Term-TermLike .SortC           = Sort-T
  Term-TermLike ._⟪$⟫_           = App
  Term-TermLike {a} {b} .byUniformFold f = helper 0
    where
      helper : 𝕀 → Term a b → Term a b
      helper k (Var-T (Bound x))  = f k x
      helper k v@(FDB _)          = v
      helper k v@(Var-T (Free _)) = v
      helper k v@(Sort-T x)       = v
      helper k v@(Const-T x)      = v
      helper k (App t t₁)         = App (helper k t) (helper k t₁)
      helper k (AppE t t₁)        = AppE (helper k t) (helper k t₁)
      helper k (Lam-P x t)        = Lam-P x (helper (suc𝕀 k) t)
      helper k (Lam-A x t t₁)     = Lam-A x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (LamE x t t₁)      = LamE x (helper k t) (helper (suc𝕀 k) t₁)
      helper k v@(Cont _ _ _)     = v
      helper k (Pi x t t₁)        = Pi x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (All x t t₁)       = All x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Iota x t t₁)      = Iota x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Eq-T t t₁)        = Eq-T (helper k t) (helper k t₁)
      helper k (M-T t)            = M-T (helper k t)
      helper k (Mu t t₁)          = Mu (helper k t) (helper k t₁)
      helper k (Epsilon t)        = Epsilon (helper k t)
      helper k (Gamma t t₁)       = Gamma (helper k t) (helper k t₁)
      helper k (Ev m args)        = Ev m (mapPrimMetaArgs (helper k) args)
      helper k (Char-T c)         = Char-T c
      helper k (CharEq t t')      = CharEq (helper k t) (helper k t')
      helper k (Pr1 t)            = Pr1 (helper k t)
      helper k (Pr2 t)            = Pr2 (helper k t)
      helper k (Beta t t')        = Beta (helper k t) (helper k t')
      helper k (Delta t t')       = Delta (helper k t) (helper k t')
      helper k (Sigma t)          = Sigma (helper k t)
      helper k (Rho t t₁ t₂)      = Rho (helper k t) (helper (suc𝕀 k) t₁) (helper k t₂)
      helper k (Pair t t₁ t₂)     = Pair (helper k t) (helper k t₁) (helper (suc𝕀 k) t₂)
      helper k (Phi t t₁ t₂)      = Phi (helper k t) (helper k t₁) (helper k t₂)
  Term-TermLike .stripBinder (All  _ t' t'') = just t''
  Term-TermLike .stripBinder (Pi   _ t' t'') = just t''
  Term-TermLike .stripBinder (Iota _ t' t'') = just t''
  Term-TermLike .stripBinder (Lam-P  _ t')   = just t'
  Term-TermLike .stripBinder (Lam-A _ _ t')  = just t'
  Term-TermLike .stripBinder (LamE _ _ t')   = just t'
  Term-TermLike .stripBinder _               = nothing

module _ {a b : Bool} where
  open TermLike (Term-TermLike {a} {b}) public

{-# TERMINATING #-}
showTermCtx : List String → Term a b → String
showTermCtx l (Var-T x)      = showVar l x
showTermCtx l (FDB x)        = "FDB" <+> show x
showTermCtx l (Sort-T x)     = show x
showTermCtx l (Const-T x)    = show x
showTermCtx l (Pr1 t)        = "π1" <+> showTermCtx l t
showTermCtx l (Pr2 t)        = "π2" <+> showTermCtx l t
showTermCtx l (Beta t t₁)    = "β" <+> showTermCtx l t <+> showTermCtx l t₁
showTermCtx l (Delta t t₁)   = "Delta" + showTermCtx l t <+> showTermCtx l t₁
showTermCtx l (Sigma t)      = "ς" + showTermCtx l t
showTermCtx l (App t t₁)     = "[" + showTermCtx l t <+> showTermCtx l t₁ + "]"
showTermCtx l (AppE t t₁)    = "<" + showTermCtx l t <+> showTermCtx l t₁ + ">"
showTermCtx l (Lam-P n t)    = "λ" <+> n + "." <+> showTermCtx (n ∷ l) t
showTermCtx l (Cont n _ t)   = "Cont" <+> n + "." <+> showTermCtx (n ∷ l) t
showTermCtx l (Rho t t₁ t₂)  = "ρ" <+> showTermCtx l t <+> ":" <+> showTermCtx l t₁ <+> showTermCtx l t₂
showTermCtx l (All n t t₁)   = "∀" <+> n <+> ":" <+> showTermCtx l t + "." <+> showTermCtx (n ∷ l) t₁
showTermCtx l (Pi n t t₁)    = "Π" <+> n <+> ":" <+> showTermCtx l t + "." <+> showTermCtx (n ∷ l) t₁
showTermCtx l (Iota n t t₁)  = "ι" <+> n <+> ":" <+> showTermCtx l t + "." <+> showTermCtx (n ∷ l) t₁
showTermCtx l (Lam-A n t t₁) = "λ" <+> n <+> ":" <+> showTermCtx l t + "." <+> showTermCtx (n ∷ l) t₁
showTermCtx l (LamE n t t₁)  = "Λ" <+> n <+> ":" <+> showTermCtx l t + "." <+> showTermCtx (n ∷ l) t₁
showTermCtx l (Pair t t₁ t₂) = "{" + showTermCtx l t + "," + showTermCtx l t₁ <+> "." <+> showTermCtx l t₂ + "}"
showTermCtx l (Phi t t₁ t₂)  = "φ" <+> showTermCtx l t <+> showTermCtx l t₁ <+> showTermCtx l t₂
showTermCtx l (Eq-T t t₁)    = "(=" <+> showTermCtx l t <+> showTermCtx l t₁ + ")"
showTermCtx l (M-T t)        = "M" <+> showTermCtx l t
showTermCtx l (Mu t t₁)      = "μ" <+> showTermCtx l t <+> showTermCtx l t₁
showTermCtx l (Epsilon t)    = "ε" <+> showTermCtx l t
showTermCtx l (Gamma t t₁)   = "Γ" <+> showTermCtx l t <+> showTermCtx l t₁
showTermCtx l (Ev m args)    = "Ev" <+> show m <+> primMetaArgs-Show (showTermCtx l) args
showTermCtx l (Char-T c)     = "'" + show c + "'"
showTermCtx l (CharEq t t')  = "CharEq" <+> showTermCtx l t <+> showTermCtx l t'

instance
  Term-Show : Show (Term a b)
  Term-Show {a} {b} = record { show = showTermCtx [] }

{-# TERMINATING #-}
Erase : AnnTerm → PureTerm b
Erase (Var-T x)      = Var-T x
Erase (Sort-T x)     = Sort-T x
Erase (Const-T x)    = Const-T x
Erase (Pr1 t)        = Erase t
Erase (Pr2 t)        = Erase t
Erase (Beta t t₁)    = Erase t₁
Erase (Delta t t₁)   = Erase t₁
Erase (Sigma t)      = Erase t
Erase (App t t₁)     = App (Erase t) (Erase t₁)
Erase (AppE t t₁)    = Erase t
Erase (Rho t t₁ t₂)  = Erase t₂
Erase (All n t t₁)   = All n (Erase t) (Erase t₁)
Erase (Pi n t t₁)    = Pi n (Erase t) (Erase t₁)
Erase (Iota n t t₁)  = Iota n (Erase t) (Erase t₁)
Erase (Lam-A n t t₁) = Lam-P n (Erase t₁)
Erase (LamE _ t t₁)  = strengthen (Erase t₁)
Erase (Pair t t₁ t₂) = Erase t
Erase (Phi t t₁ t₂)  = Erase t₂
Erase (Eq-T x x₁)    = Eq-T (Erase x) (Erase x₁)
Erase (M-T t)        = M-T (Erase t)
Erase (Mu t t₁)      = Mu (Erase t) (Erase t₁)
Erase (Epsilon t)    = Epsilon (Erase t)
Erase (Gamma t t₁)   = Gamma (Erase t) (Erase t₁)
Erase (Ev m args)    = Ev m (mapPrimMetaArgs Erase args)
Erase (Char-T c)     = Char-T c
Erase (CharEq x x₁)  = CharEq (Erase x) (Erase x₁)

condErase : AnnTerm → Term a false
condErase {false} t = Erase t
condErase {true}  t = t
