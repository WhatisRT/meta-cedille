module Theory.Normalisation where

open import Prelude
open import Prelude.Nat

open import Theory.NBE using () renaming (nf to normalizePure; hnf to hnfNormPure) public
open import Theory.Terms
open import Theory.Context

-- don't have NBE for annotated terms yet
-- not a big deal, since it's not used much anyway

-- something in is head normal form, if its outermost constructor is not one of the following: Var-A (if the lookup fails), App-A, AppE-A
{-# TERMINATING #-}
hnfNorm : Context → AnnTerm → AnnTerm
hnfNorm Γ v@(Var-A x) with lookupInContext x Γ
... | just record { def = just x }        = hnfNorm Γ x
... | just _            = v -- we cannot reduce axioms
... | nothing           = v -- in case the lookup fails, we cannot reduce
hnfNorm Γ (App-A t t₁)  = maybe (λ t' → hnfNorm Γ $ subst t' t₁) (t ⟪$⟫ t₁) $ stripBinder (hnfNorm Γ t)
hnfNorm Γ (AppE-A t t₁) = maybe (λ t' → hnfNorm Γ $ subst t' t₁) (t ⟪$⟫ t₁) $ stripBinder (hnfNorm Γ t)
{-# CATCHALL #-}
hnfNorm Γ v             = v
