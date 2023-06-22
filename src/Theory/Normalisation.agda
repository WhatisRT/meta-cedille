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
hnfNorm Γ (App b t t₁)   = maybe (λ t' → hnfNorm Γ $ subst t' t₁) (App b t t₁) $ stripBinder (hnfNorm Γ t)
hnfNorm Γ v@(CharEq _ _) = normalize Γ v -- reduce to a bool, if possible
hnfNorm Γ (Pr1 t)        = hnfNorm Γ t
hnfNorm Γ (Pr2 t)        = hnfNorm Γ t
hnfNorm Γ (Beta _ t)     = hnfNorm Γ t
hnfNorm Γ (Delta _ t)    = hnfNorm Γ t
hnfNorm Γ (Sigma t)      = hnfNorm Γ t
hnfNorm Γ (Rho _ _ t)    = hnfNorm Γ t
hnfNorm Γ (Pair t _ _)   = hnfNorm Γ t
hnfNorm Γ (Phi _ _ t)    = hnfNorm Γ t
{-# CATCHALL #-}
hnfNorm Γ v              = v

{-# NON_TERMINATING #-}
normalize Γ v@(Var-T x) with lookupInContext x Γ
... | just record { def = just x } = normalize Γ $ condErase x
... | just _                          = v -- we cannot reduce axioms
... | nothing                         = v -- in case the lookup fails, we cannot reduce
normalize Γ v@(Sort-T x)              = v
normalize Γ v@(Const-T x)             = v
normalize Γ (App b t t₁) with hnfNorm Γ t
... | t'                              = case stripBinder t' of λ where
    (just t'') → normalize Γ (subst t'' t₁)
    nothing    → App b (normalize Γ t') (normalize Γ t₁)
normalize Γ (Lam-P b n t) with normalize Γ t
... | t''@(App _ t' (Var-T (Bound i)))  = if i ≣ 0 ∧ validInContext t' Γ
  then normalize Γ (strengthen t') else Lam-P b n t'' -- eta reduce here
... | t''                             = Lam-P b n t''
normalize Γ (Lam-A b n t t₁) with normalize Γ t₁
... | t''@(App _ t' (Var-T (Bound i)))  = if i ≣ 0 ∧ validInContext t' Γ
  then normalize Γ (strengthen t') else Lam-A b n t t'' -- eta reduce here
... | t''                             = Lam-A b n t t''
normalize Γ (Pi b n t t₁)             = Pi b n (normalize Γ t) (normalize Γ t₁)
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
normalize Γ (Pr1 t)                   = normalize Γ t
normalize Γ (Pr2 t)                   = normalize Γ t
normalize Γ (Beta _ t)                = normalize Γ t
normalize Γ (Delta _ t)               = normalize Γ t
normalize Γ (Sigma t)                 = normalize Γ t
normalize Γ (Rho _ _ t)               = normalize Γ t
normalize Γ (Pair t _ _)              = normalize Γ t
normalize Γ (Phi _ _ t)               = normalize Γ t
