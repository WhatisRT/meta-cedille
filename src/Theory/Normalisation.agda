{-# OPTIONS --type-in-type #-}
module Theory.Normalisation where

open import Prelude
open import Prelude.Nat

open import Theory.NBE using () renaming (nf to normalizePure; hnf to hnfNormPure) public
open import Theory.Terms
open import Theory.Context

private variable
  A : Set
  a b : Bool

-- don't have NBE for annotated terms yet
-- not a big deal, since it's not used much anyway

unsafeDebugLog : String → A → A
unsafeDebugLog s x = unsafePerformIO (putStr (s + "\n") >> return x)

stripLambdas : BinderType a → Term a false → Maybe (Term a false)
stripLambdas b       (Lam-P _ _ t)           = just t
stripLambdas Regular (Lam-A Regular _ _ t)   = just t
stripLambdas Regular (Lam-A Erased  _ _ t)   = stripLambdas Regular t
stripLambdas Erased  t@(Lam-A Regular _ _ _) = just t
stripLambdas Erased  (Lam-A Erased  _ _ t)   = just t
stripLambdas b       t                       = nothing

module Norm (doLog : Bool) where

  log : Term a false → Term b false → A → A
  log t t' x = if doLog
    then unsafePerformIO (putStr (show t <+> "~>" <+> show t' + "\n") >> return x)
    else x

  -- something in is head normal form, if its outermost constructor is not one of the following: Var-A (if the lookup fails), App, AppE
  hnfNorm normalize : Context → Term a false → Term a false

  {-# NON_TERMINATING #-}
  hnfNorm Γ v@(Var-T x) with lookupInContext x Γ
  ... | just record { def = just x } = log v x $ hnfNorm Γ $ condErase x
  ... | just _             = v -- we cannot reduce axioms
  ... | nothing            = v -- in case the lookup fails, we cannot reduce
  hnfNorm Γ v@(App b t t₁) = maybe
    (λ t' → log v (subst t' t₁) $ hnfNorm Γ $ subst t' t₁)
    (App b t t₁) $ stripLambdas b (hnfNorm Γ t)
  hnfNorm Γ v@(CharEq _ _) = normalize Γ v -- reduce to a bool, if possible
  hnfNorm Γ v@(Pr1 t)      = log v t $ hnfNorm Γ t
  hnfNorm Γ v@(Pr2 t)      = log v t $ hnfNorm Γ t
  hnfNorm Γ v@(Beta _ t)   = log v t $ hnfNorm Γ t
  hnfNorm Γ v@(Delta _ t)  = log v t $ hnfNorm Γ t
  hnfNorm Γ v@(Sigma t)    = log v t $ hnfNorm Γ t
  hnfNorm Γ v@(Rho _ _ t)  = log v t $ hnfNorm Γ t
  hnfNorm Γ v@(Pair t _ _) = log v t $ hnfNorm Γ t
  hnfNorm Γ v@(Phi _ _ t)  = log v t $ hnfNorm Γ t
  {-# CATCHALL #-}
  hnfNorm Γ v              = v

  {-# NON_TERMINATING #-}
  normalize Γ v@(Var-T x) with lookupInContext x Γ
  ... | just record { def = just x }    = log v x $ normalize Γ $ condErase x
  ... | just _                          = v -- we cannot reduce axioms
  ... | nothing                         = v -- in case the lookup fails, we cannot reduce
  normalize Γ v@(Sort-T x)              = v
  normalize Γ v@(Const-T x)             = v
  normalize Γ v@(App b t t₁) with hnfNorm Γ t
  ... | t'                              = case stripLambdas b t' of λ where
      (just t'') → log v (subst t'' t₁) $ normalize Γ (subst t'' t₁)
      nothing    → App b (normalize Γ t') (normalize Γ t₁)
  normalize Γ v@(Lam-P b n t) with normalize Γ t
  ... | t''@(App _ t' (Var-T (Bound i)))  = if i ≣ 0 ∧ validInContext t' Γ
    then log v (strengthen t') $ normalize Γ (strengthen t') else Lam-P b n t'' -- eta reduce here
  ... | t''                             = Lam-P b n t''
  normalize Γ v@(Lam-A b n t t₁) with normalize Γ t₁
  ... | t''@(App _ t' (Var-T (Bound i)))  = if i ≣ 0 ∧ validInContext t' Γ
    then log v (strengthen t') $ normalize Γ (strengthen t') else Lam-A b n t t'' -- eta reduce here
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
  normalize Γ v@(Pr1 t)                   = log v t $ normalize Γ t
  normalize Γ v@(Pr2 t)                   = log v t $ normalize Γ t
  normalize Γ v@(Beta _ t)                = log v t $ normalize Γ t
  normalize Γ v@(Delta _ t)               = log v t $ normalize Γ t
  normalize Γ v@(Sigma t)                 = log v t $ normalize Γ t
  normalize Γ v@(Rho _ _ t)               = log v t $ normalize Γ t
  normalize Γ v@(Pair t _ _)              = log v t $ normalize Γ t
  normalize Γ v@(Phi _ _ t)               = log v t $ normalize Γ t

hnfNorm = Norm.hnfNorm false
normalize = Norm.normalize false
