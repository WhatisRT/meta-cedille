module Theory.Normalisation where

open import Prelude
open import Prelude.Nat

open import Theory.NBE using () renaming (nf to normalizePure; hnf to hnfNormPure) public
open import Theory.Terms
open import Theory.Context

-- don't have NBE for annotated terms yet
-- not a big deal, since it's not used much anyway

-- something in is head normal form, if its outermost constructor is not one of the following: Var-A (if the lookup fails), App, AppE
hnfNorm normalize : ∀ {a} → Context → Term a false → Term a false

{-# NON_TERMINATING #-}
hnfNorm Γ v@(Var-T x) with lookupInContext x Γ
... | just record { def = just x } = hnfNorm Γ $ condErase x
... | just _             = v -- we cannot reduce axioms
... | nothing            = v -- in case the lookup fails, we cannot reduce
hnfNorm Γ (App t t₁)     = maybe (λ t' → hnfNorm Γ $ subst t' t₁) (t ⟪$⟫ t₁)  $ stripBinder (hnfNorm Γ t)
hnfNorm Γ (AppE t t₁)    = maybe (λ t' → hnfNorm Γ $ subst t' t₁) (AppE t t₁) $ stripBinder (hnfNorm Γ t)
hnfNorm Γ v@(CharEq _ _) = normalize Γ v -- reduce to a bool, if possible
{-# CATCHALL #-}
hnfNorm Γ v              = v

{-# NON_TERMINATING #-}
normalize Γ v@(Var-T x) with lookupInContext x Γ
... | just record { def = just x } = normalize Γ $ condErase x
... | just _                          = v -- we cannot reduce axioms
... | nothing                         = v -- in case the lookup fails, we cannot reduce
normalize Γ v@(Sort-T x)              = v
normalize Γ v@(Const-T x)             = v
normalize Γ (App t t₁) with hnfNorm Γ t
... | t'                              = case stripBinder t' of λ where
    (just t'') → normalize Γ (subst t'' t₁)
    nothing    → normalize Γ t' ⟪$⟫ normalize Γ t₁
normalize Γ (AppE t t₁) with hnfNorm Γ t
... | t'                              = case stripBinder t' of λ where
    (just t'') → normalize Γ (subst t'' t₁)
    nothing    → AppE (normalize Γ t') (normalize Γ t₁)
normalize Γ (Lam-P n t) with normalize Γ t
... | t''@(App t' (Var-T (Bound i)))  = if i ≣ 0 ∧ validInContext t' Γ
  then normalize Γ (strengthen t') else Lam-P n t'' -- eta reduce here
... | t''                             = Lam-P n t''
normalize Γ (Lam-A n t t₁) with normalize Γ t₁
... | t''@(App t' (Var-T (Bound i)))  = if i ≣ 0 ∧ validInContext t' Γ
  then normalize Γ (strengthen t') else Lam-A n t t'' -- eta reduce here
... | t''                             = Lam-A n t t''
normalize Γ (LamE n t t₁) with normalize Γ t₁
... | t''@(AppE t' (Var-T (Bound i))) = if i ≣ 0 ∧ validInContext t' Γ
  then normalize Γ (strengthen t') else LamE n t t'' -- eta reduce here
... | t''                             = LamE n t t''
normalize Γ (Pi n t t₁)               = Pi n (normalize Γ t) (normalize Γ t₁)
normalize Γ (All n t t₁)              = All n (normalize Γ t) (normalize Γ t₁)
normalize Γ (Iota n t t₁)             = Iota n (normalize Γ t) (normalize Γ t₁)
normalize Γ (Eq-T t t₁)               = Eq-T (normalize Γ t) (normalize Γ t₁)
normalize Γ (M-T t)                   = M-T (normalize Γ t)
normalize Γ (Mu t t₁)                 = Mu (normalize Γ t) (normalize Γ t₁)
normalize Γ (Epsilon t)               = Epsilon (normalize Γ t)
normalize Γ (Gamma t t₁)              = Gamma (normalize Γ t) (normalize Γ t₁)
normalize Γ (Ev m args)               = Ev m (mapPrimMetaArgs (normalize Γ) args)
normalize Γ (Char-T c)                = (Char-T c)
normalize Γ (CharEq t t₁) with normalize Γ t | normalize Γ t₁
... | (Char-T c) | (Char-T c')        = normalize Γ $ FreeVar $ show (c ≣ c')
{-# CATCHALL #-}
... | x | x₁                          = CharEq x x₁
normalize Γ (Pr1 t)                   = Pr1 (normalize Γ t)
normalize Γ (Pr2 t)                   = Pr2 (normalize Γ t)
normalize Γ (Beta t t₁)               = Beta (normalize Γ t) (normalize Γ t₁)
normalize Γ (Delta t t₁)              = Delta (normalize Γ t) (normalize Γ t₁)
normalize Γ (Sigma t)                 = Sigma (normalize Γ t)
normalize Γ (Rho t t₁ t₂)             = Rho (normalize Γ t) (normalize Γ t₁) (normalize Γ t₂) -- TODO: extend Γ?
normalize Γ (Pair t t₁ t₂)            = Pair (normalize Γ t) (normalize Γ t₁) (normalize Γ t₂) -- TODO: extend Γ?
normalize Γ (Phi t t₁ t₂)             = Phi (normalize Γ t) (normalize Γ t₁) (normalize Γ t₂)
