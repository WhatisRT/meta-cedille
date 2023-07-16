--------------------------------------------------------------------------------
-- Annotated and pure trems and basic term-related functions
--------------------------------------------------------------------------------

module Theory.Terms where

open import Prelude
open import Prelude.Nat
open import Unsafe

open import Theory.Const public
open import Theory.Names public
open import Theory.PrimMeta public

private variable a b : Bool

data BinderType : @0 Bool → Set where
  Regular : BinderType a
  Erased  : BinderType true

instance
  Binder-EqB : EqB (BinderType a)
  Binder-EqB ._≣_ Regular Regular = true
  Binder-EqB ._≣_ Erased  Erased  = true
  Binder-EqB ._≣_ _ _ = false

  Binder-Show : Show (BinderType a)
  Binder-Show .show Regular = "Regular"
  Binder-Show .show Erased  = "Erased"

ΣBinderType = Σ Bool (λ b → BinderType b)

-- the second bool decides whether to have the NBE constructors
data Term : @0 Bool → @0 Bool → Set where
  Var     : Name → Term a b
  FDB     : 𝕀 → Term a true
  Sort-T  : Sort → Term a b
  Const-T : Const → Term a false
  Const-N : Const → ℕ → Term a true
  App     : BinderType a → Term a b → Term a b → Term a b
  Lam-P   : BinderType false → String → Term false b → Term false b
  Lam-A   : BinderType true  → String → Term true b → Term true b → Term true b
  Cont    : String → List (String × Maybe (Term a true)) → Term a true → Term a true
  Pi      : BinderType true → String → Term a b → Term a b → Term a b
  Iota    : String → Term a b → Term a b → Term a b
  Eq-T    : Term a b → Term a b → Term a b
  M-T     : Term a b → Term a b
  Mu      : Term a b → Term a b → Term a b
  Epsilon : Term a b → Term a b
  Ev      : (m : PrimMeta) → primMetaArgs (Term a b) m → Term a b
  Pr1     : Term true b → Term true b
  Pr2     : Term true b → Term true b
  Beta    : Term true b → Term true b → Term true b -- proves first arg eq, erase to second arg
  Delta   : Term true b → Term true b → Term true b -- inhabits first arg if snd arg proves false
  Sigma   : Term true b → Term true b
  Rho     : Term true b → Term true b → Term true b → Term true b -- first arg is eq, rewrite the name in the third arg and inhabit with fourth arg
  Pair    : Term true b → Term true b → Term true b → Term true b
  Phi     : Term true b → Term true b → Term true b → Term true b
  -- there is a let binding here, which is probably unnecessary

pattern App-R t t'    = App Regular t t'
pattern App-E t t'    = App Erased  t t'
pattern Char-T c      = Const-T (CharC c)
pattern Char-T' c     = Const-N (CharC c) _
pattern App2 t t' t'' = App-R (App-R t t') t''
pattern CharEq-T t t' = App2 (Const-T CharEq) t t'
pattern M-T' t        = App-R (Const-T MM) t
pattern MuM-T t t'    = App2 (Const-T MuM) t t'
pattern EpsilonM-T t  = App-R (Const-T EpsilonM) t
pattern CatchM-T t t' = App2 (Const-T CatchM) t t'

infixr 0 _⟪→⟫_ _⟪⇒⟫_
infixl -1 _⟪$⟫_

pattern _⟪→⟫_ t t' = Pi Regular "" t t'
pattern _⟪⇒⟫_ t t' = Pi Erased  "" t t'
pattern _⟪$⟫_ t t' = App-R t t'

pattern ⋆ = Sort-T Ast
pattern □ = Sort-T Sq

pattern BoundVar x = Var (Bound x)
pattern FreeVar x  = Var (Free x)

module _ {a b : Bool} where
  module P = Types {Term a b} FreeVar ⋆ _⟪$⟫_

open P public

PureTerm : @0 Bool → Set
PureTerm = Term false

AnnTerm : Set
AnnTerm = Term true false

Const-T' : Const → Term a b
Const-T' {b = false} c = Const-T c
Const-T' {b = true}  c = Const-N c 0

stripBinder : Term a b → Maybe (Term a b)
stripBinder (Pi _ _ t' t'')  = just t''
stripBinder (Iota _ t' t'')  = just t''
stripBinder (Lam-P _ _ t')   = just t'
stripBinder (Lam-A _ _ _ t') = just t'
stripBinder _                = nothing

private
  {-# TERMINATING #-}
  byUniformFold : (𝕀 → 𝕀 → Term a b) → Term a b → Term a b
  byUniformFold {a = a} {b} f = helper 0
    where
      helper : 𝕀 → Term a b → Term a b
      helper k (Var (Bound x))  = f k x
      helper k v@(FDB _)        = v
      helper k v@(Var (Free _)) = v
      helper k v@(Sort-T x)     = v
      helper k (Const-T x)      = Const-T x
      helper k (Const-N x n)    = Const-N x n
      helper k (App b t t₁)     = App b (helper k t) (helper k t₁)
      helper k (Lam-P b x t)    = Lam-P b x (helper (suc𝕀 k) t)
      helper k (Lam-A b x t t₁) = Lam-A b x (helper k t) (helper (suc𝕀 k) t₁)
      helper k v@(Cont _ _ _)   = v
      helper k (Pi b x t t₁)    = Pi b x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Iota x t t₁)    = Iota x (helper k t) (helper (suc𝕀 k) t₁)
      helper k (Eq-T t t₁)      = Eq-T (helper k t) (helper k t₁)
      helper k (M-T t)          = M-T (helper k t)
      helper k (Mu t t₁)        = Mu (helper k t) (helper k t₁)
      helper k (Epsilon t)      = Epsilon (helper k t)
      helper k (Ev m args)      = Ev m (mapPrimMetaArgs (helper k) args)
      helper k (Pr1 t)          = Pr1 (helper k t)
      helper k (Pr2 t)          = Pr2 (helper k t)
      helper k (Beta t t')      = Beta (helper k t) (helper k t')
      helper k (Delta t t')     = Delta (helper k t) (helper k t')
      helper k (Sigma t)        = Sigma (helper k t)
      helper k (Rho t t₁ t₂)    = Rho (helper k t) (helper (suc𝕀 k) t₁) (helper k t₂)
      helper k (Pair t t₁ t₂)   = Pair (helper k t) (helper k t₁) (helper (suc𝕀 k) t₂)
      helper k (Phi t t₁ t₂)    = Phi (helper k t) (helper k t₁) (helper k t₂)

  modifyIndices : 𝕀 → Term a b → Term a b
  modifyIndices n = byUniformFold λ k x → BoundVar $ if x <𝕀 k then x else pred𝕀 (x +𝕀 n)

weakenBy : 𝕀 → Term a b → Term a b
weakenBy i = modifyIndices (suc𝕀 i)

strengthen : Term a b → Term a b
strengthen = modifyIndices 0

-- substitute the first unbound variable in t with t'
subst : Term a b → Term a b → Term a b
subst t t' = strengthen $ byUniformFold
  (λ k x → if k ≣ x then weakenBy (suc𝕀 k) t' else BoundVar x) t

module _ where

  private
    showBinderL : BinderType a → String
    showBinderL Regular = "λ"
    showBinderL Erased  = "Λ"

    showBinderP : BinderType true → String × String
    showBinderP Regular = ("→"   , "Π")
    showBinderP Erased  = ("=>"  , "∀")

  {-# TERMINATING #-}
  showTermCtx : List String → Term a b → String
  showTermCtx l (Var x)          = showVar l x
  showTermCtx l (FDB x)          = "FDB" <+> show x
  showTermCtx l (Sort-T x)       = show x
  showTermCtx l (Const-T x)      = show x
  showTermCtx l (Const-N x n)    = "NBE" + show x + show n
  showTermCtx l (Pr1 t)          = "π1" <+> showTermCtx l t
  showTermCtx l (Pr2 t)          = "π2" <+> showTermCtx l t
  showTermCtx l (Beta t t₁)      = "β" <+> showTermCtx l t <+> showTermCtx l t₁
  showTermCtx l (Delta t t₁)     = "δ" <+> showTermCtx l t <+> showTermCtx l t₁
  showTermCtx l (Sigma t)        = "ς" <+> showTermCtx l t
  showTermCtx l (App-R t t₁)     = "[" + showTermCtx l t <+> showTermCtx l t₁ + "]"
  showTermCtx l (App-E t t₁)     = "<" + showTermCtx l t <+> showTermCtx l t₁ + ">"
  showTermCtx l (Lam-P b n t)    = showBinderL b <+> n + "." <+> showTermCtx (n ∷ l) t
  showTermCtx l (Lam-A b n t t₁) = showBinderL b <+> n <+> ":" <+> showTermCtx l t + "." <+> showTermCtx (n ∷ l) t₁
  showTermCtx l (Cont n _ t)     = "Cont" <+> n + "." <+> showTermCtx (n ∷ l) t
  showTermCtx l (Rho t t₁ t₂)    = "ρ" <+> showTermCtx l t <+> ":" <+> showTermCtx ("_" ∷ l) t₁ <+> showTermCtx l t₂
  showTermCtx l (Pi b n t t₁)    = if n ≣ "_" ∨ n ≣ ""
    then "(" + showTermCtx l t + ")" <+> proj₁ (showBinderP b) <+> showTermCtx (n ∷ l) t₁
    else proj₂ (showBinderP b) <+> n <+> ":" <+> showTermCtx l t + "." <+> showTermCtx (n ∷ l) t₁
  showTermCtx l (Iota n t t₁)    = "ι" <+> n <+> ":" <+> showTermCtx l t + "." <+> showTermCtx (n ∷ l) t₁
  showTermCtx l (Pair t t₁ t₂)   = "{" + showTermCtx l t + "," + showTermCtx l t₁ <+> "." <+> showTermCtx l t₂ + "}"
  showTermCtx l (Phi t t₁ t₂)    = "φ" <+> showTermCtx l t <+> showTermCtx l t₁ <+> showTermCtx l t₂
  showTermCtx l (Eq-T t t₁)      = "(=" <+> showTermCtx l t <+> showTermCtx l t₁ + ")"
  showTermCtx l (M-T t)          = "M" <+> showTermCtx l t
  showTermCtx l (Mu t t₁)        = "μ" <+> showTermCtx l t <+> showTermCtx l t₁
  showTermCtx l (Epsilon t)      = "ε" <+> showTermCtx l t
  showTermCtx l (Ev m args)      = "Ev" <+> show m <+> primMetaArgs-Show (showTermCtx l) args

instance
  Term-Show : Show (Term a b)
  Term-Show {a} {b} = record { show = showTermCtx [] }

evalConst : (Term a b → Term a b) → Term a b → Term a b
evalConst reduce v@(CharEq-T t t') with reduce t | reduce t'
... | Char-T c | Char-T c' = reduce $ Var $ Free $ show (c ≣ c')
... | _        | _         = v
evalConst reduce t = t

evalConst' : (Term a b → Term a b) → Const → Term a b
evalConst' reduce CharEq with reduce (BoundVar 0) | reduce (BoundVar 1)
... | Char-T  c | Char-T  c' = reduce $ Var $ Free $ show (c ≣ c')
... | Char-T' c | Char-T' c' = reduce $ Var $ Free $ show (c ≣ c')
... | t         | t'         = (Const-T' CharEq) ⟪$⟫ t ⟪$⟫ t'
evalConst' reduce MM         = (Const-T' MM) ⟪$⟫ reduce (BoundVar 0)
evalConst' reduce MuM        = (Const-T' MuM) ⟪$⟫ reduce (BoundVar 1) ⟪$⟫ reduce (BoundVar 0)
evalConst' reduce EpsilonM   = (Const-T' EpsilonM) ⟪$⟫ reduce (BoundVar 0)
evalConst' reduce CatchM     = (Const-T' CatchM) ⟪$⟫ reduce (BoundVar 1) ⟪$⟫ reduce (BoundVar 0)
evalConst' reduce c          = Const-T' c

{-# TERMINATING #-}
Erase : Term true b → PureTerm b
Erase (Var x)                = Var x
Erase (FDB x)                = FDB x
Erase (Sort-T x)             = Sort-T x
Erase (Const-T x)            = Const-T x
Erase (Const-N x n)          = Const-N x n
Erase (App-R t t₁)           = App-R (Erase t) (Erase t₁)
Erase (App-E t t₁)           = Erase t
Erase (Pi b n t t₁)          = Pi b n (Erase t) (Erase t₁)
Erase (Iota n t t₁)          = Iota n (Erase t) (Erase t₁)
Erase (Lam-A Regular n t t₁) = Lam-P Regular n (Erase t₁)
Erase (Lam-A Erased n t t₁)  = strengthen (Erase t₁)
Erase (Cont n Γ x)           = error "Erase cont"
Erase (Pr1 t)                = Erase t
Erase (Pr2 t)                = Erase t
Erase (Beta t t₁)            = Erase t₁
Erase (Delta t t₁)           = Erase t₁
Erase (Sigma t)              = Erase t
Erase (Rho t t₁ t₂)          = Erase t₂
Erase (Pair t t₁ t₂)         = Erase t
Erase (Phi t t₁ t₂)          = Erase t₂
Erase (Eq-T x x₁)            = Eq-T (Erase x) (Erase x₁)
Erase (M-T t)                = M-T (Erase t)
Erase (Mu t t₁)              = Mu (Erase t) (Erase t₁)
Erase (Epsilon t)            = Epsilon (Erase t)
Erase (Ev m args)            = Ev m (mapPrimMetaArgs Erase args)

condErase : AnnTerm → Term a false
condErase {false} t = Erase t
condErase {true}  t = t
