--------------------------------------------------------------------------------
-- This file provides the data structures and functions for the theory of
-- cedille core extended with the constructs for metaprogramming.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module CoreTheory where

import Data.Product

open import Class.Map
open import Class.Monad.Except
open import Data.HSTrie
open import Data.Word using (toℕ; fromℕ)
open import Monads.Except

open import Prelude
open import Prelude.Nat

open import Theory.Names public
open import Theory.TermLike public
open import Theory.PrimMeta public
open import Theory.Terms public

private
  variable
    A B C : Set
    M : Set → Set

data Def : Set where
  Let : AnnTerm → AnnTerm → Def
  Axiom : AnnTerm → Def

instance
  Def-Show : Show Def
  Def-Show .show (Let x x₁) = " :=" <+> show x <+> ":" <+> show x₁
  Def-Show .show (Axiom x) = " :" <+> show x

private
  data EfficientDef : Set where
    EfficientLet : AnnTerm → PureTerm → AnnTerm → EfficientDef
    EfficientAxiom : AnnTerm → EfficientDef

  toDef : EfficientDef → Def
  toDef (EfficientLet x x₁ x₂)   = Let x x₂
  toDef (EfficientAxiom x)       = Axiom x

  getNorm : EfficientDef → Maybe PureTerm
  getNorm (EfficientLet x x₁ x₂) = return x₁
  getNorm (EfficientAxiom x)     = nothing

  typeOfDef : Def → AnnTerm
  typeOfDef (Let _ x) = x
  typeOfDef (Axiom x) = x

GlobalContext : Set
GlobalContext = HSTrie EfficientDef

emptyGlobalContext : GlobalContext
emptyGlobalContext = emptyMap

Context : Set
Context = GlobalContext × List AnnTerm

private
  instance
    Context-Show : Show Context
    Context-Show .show (fst , snd) = (show $ length snd) <+> "local variables:" + show snd

globalToContext : GlobalContext → Context
globalToContext Γ = Γ , []

contextToGlobal : Context → GlobalContext
contextToGlobal (fst , snd) = fst

private
  -- add variable to context, so that index 0 points to that variable
  pushVar : AnnTerm → Context → Context
  pushVar v (fst , snd) = fst , v ∷ snd

  localContextLength : Context → ℕ
  localContextLength (fst , snd) = length snd

  efficientLookupInContext : Name → Context → Maybe EfficientDef
  efficientLookupInContext (Bound x) (fst , snd) =
    EfficientAxiom ∘ weakenBy (suc𝕀 x) <$> lookupMaybe (toℕ x) snd
  efficientLookupInContext (Free x) (fst , snd) = lookup x fst

  lookupInContext : Name → Context → Maybe Def
  lookupInContext n Γ = toDef <$> efficientLookupInContext n Γ

  {-# TERMINATING #-}
  validInContext : PureTerm → Context → Bool
  validInContext = helper 0
    where
      -- instead of modifying the context here, we just count how many variables we would have added if we did
      helper : 𝕀 → PureTerm → Context → Bool
      helper k (Var-P (Bound x)) Γ = x <𝕀 (fromℕ (localContextLength Γ) +𝕀 k)
      helper k (Var-P n@(Free x)) Γ = maybe (λ _ → true) false $ lookupInContext n Γ
      helper k (Sort-P x) Γ = true
      helper k (Const-P x) Γ = true
      helper k (App-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
      helper k (Lam-P _ t) Γ = helper (suc𝕀 k) t Γ
      helper k (Pi-P _ t t₁) Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
      helper k (All-P _ t t₁) Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
      helper k (Iota-P _ t t₁) Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
      helper k (Eq-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
      helper k (M-P t) Γ = helper k t Γ
      helper k (Mu-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
      helper k (Epsilon-P t) Γ = helper k t Γ
      helper k (Gamma-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
      helper k (Ev-P m t) Γ = primMetaArgsAnd $ mapPrimMetaArgs (λ x → helper k x Γ) t
      helper k (Char-P c) Γ = true
      helper k (CharEq-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ

  {-# TERMINATING #-}
  checkFree : Name → PureTerm → Bool
  checkFree = helper 0
    where
      helper : 𝕀 → Name → PureTerm → Bool
      helper k n (Var-P (Bound x)) = case n of λ where
        (Bound x₁) → x ≣ (k +𝕀 x₁)
        (Free x₁) → false
      helper k n (Var-P (Free x)) = case n of λ where
        (Bound x₁) → false
        (Free x₁) → x ≣ x₁
      helper k n (Sort-P x) = false
      helper k n (Const-P x) = false
      helper k n (App-P t t₁) = helper k n t ∧ helper k n t₁
      helper k n (Lam-P _ t) = helper (suc𝕀 k) n t
      helper k n (Pi-P _ t t₁) = helper k n t ∧ helper (suc𝕀 k) n t₁
      helper k n (All-P _ t t₁) = helper k n t ∧ helper (suc𝕀 k) n t₁
      helper k n (Iota-P _ t t₁) = helper k n t ∧ helper (suc𝕀 k) n t₁
      helper k n (Eq-P t t₁) = helper k n t ∧ helper k n t₁
      helper k n (M-P t) = helper k n t
      helper k n (Mu-P t t₁) = helper k n t ∧ helper k n t₁
      helper k n (Epsilon-P t) = helper k n t
      helper k n (Gamma-P t t₁) = helper k n t ∧ helper k n t₁
      helper k n (Ev-P m t) = primMetaArgsAnd $ mapPrimMetaArgs (helper k n) t
      helper k n (Char-P c) = false
      helper k n (CharEq-P t t₁) = helper k n t ∧ helper k n t₁

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

hnfNormPure normalizePure : Context → PureTerm → PureTerm

{-# NON_TERMINATING #-}
hnfNormPure Γ v@(Var-P x) with lookupInContext x Γ
... | just (Let x₁ x₂)         = hnfNormPure Γ $ Erase x₁
... | just (Axiom x₁)          = v -- we cannot reduce axioms
... | nothing                  = v -- in case the lookup fails, we cannot reduce
hnfNormPure Γ v@(App-P t t₁) with stripBinder (hnfNormPure Γ t)
... | (just t')                = hnfNormPure Γ $ subst t' t₁
... | nothing                  = v
hnfNormPure Γ v@(CharEq-P _ _) = normalizePure Γ v -- reduce to a bool, if possible
{-# CATCHALL #-}
hnfNormPure Γ v                = v

{-# NON_TERMINATING #-}
normalizePure Γ v@(Var-P x) with efficientLookupInContext x Γ
... | just (EfficientLet x₁ x₂ x₃) = x₂
... | just (EfficientAxiom x₁)     = v -- we cannot reduce axioms
... | nothing                      = v -- in case the lookup fails, we cannot reduce
normalizePure Γ v@(Sort-P x)       = v
normalizePure Γ v@(Const-P x)      = v
normalizePure Γ (App-P t t₁) with hnfNormPure Γ t
...| t' = case stripBinder t' of λ where
    (just t'') → normalizePure Γ (subst t'' t₁)
    nothing    → normalizePure Γ t' ⟪$⟫ normalizePure Γ t₁
normalizePure Γ (Lam-P n t) with normalizePure Γ t
... | t''@(App-P t' (Var-P (Bound i))) = if i ≣ 0 ∧ validInContext t' Γ
  then normalizePure Γ (strengthen t') else Lam-P n t'' -- eta reduce here
... | t'' = Lam-P n t''
normalizePure Γ (Pi-P n t t₁)      = Pi-P n (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (All-P n t t₁)     = All-P n (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Iota-P n t t₁)    = Iota-P n (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Eq-P t t₁)        = Eq-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (M-P t)            = M-P (normalizePure Γ t)
normalizePure Γ (Mu-P t t₁)        = Mu-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Epsilon-P t)      = Epsilon-P (normalizePure Γ t)
normalizePure Γ (Gamma-P t t₁)     = Gamma-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Ev-P m args)      = Ev-P m (mapPrimMetaArgs (normalizePure Γ) args)
normalizePure Γ (Char-P c)         = (Char-P c)
normalizePure Γ (CharEq-P t t₁) with normalizePure Γ t | normalizePure Γ t₁
... | (Char-P c) | (Char-P c')     = normalizePure Γ $ FreeVar $ show (c ≣ c')
{-# CATCHALL #-}
... | x | x₁                       = CharEq-P x x₁

insertInGlobalContext : GlobalName → Def → GlobalContext → String ⊎ GlobalContext
insertInGlobalContext n d Γ =
  if is-just $ lookup n Γ
    then inj₁ ("The name" <+> n <+> "is already defined!")
    else (inj₂ $ insert n (toEfficientDef d Γ) Γ)
  where
    toEfficientDef : Def → GlobalContext → EfficientDef
    toEfficientDef (Let x x₁) Γ = EfficientLet x (normalizePure (globalToContext Γ) $ Erase x) x₁
    toEfficientDef (Axiom x) Γ = EfficientAxiom x

private
  beqMonadHelper : {{_ : EqB A}} {{_ : Show A}} {{_ : Monad M}} {{_ : MonadExcept M String}}
                → A → A → String → M ⊤
  beqMonadHelper a a' s =
    if a ≣ a'
      then return tt
      else throwError (s <+> show a <+> "isn't equal to" <+> s <+> show a')

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
  ... | no  _    = throwError $ show m <+> "and" <+> show m' <+> "aren't equal!"
  pureTermBeq (Char-P c) (Char-P c') = beqMonadHelper c c' "Char"
  pureTermBeq (CharEq-P t t₁) (CharEq-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  {-# CATCHALL #-}
  pureTermBeq t t' =
    throwError $ "The terms" <+> show t <+> "and" <+> show t' <+> "aren't equal!"

module _ {{_ : Monad M}} {{_ : MonadExcept M String}} (Γ : Context) where
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
        throwError $ "The terms" <+> show t <+> "and" <+> show t' <+> "aren't equal!"

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
      compareHnfs (Lam-P _ t) t₁ = case normalizePure Γ t of λ where
        t''@(App-P t' (Var-P (Bound i))) → if i ≣ 0 ∧ validInContext t' Γ
          then (compareHnfs (strengthen t') t₁) else hnfError t'' t₁
        t'' → hnfError t'' t₁
      compareHnfs t (Lam-P _ t₁) = case normalizePure Γ t₁ of λ where
        t''@(App-P t' (Var-P (Bound i))) → if i ≣ 0 ∧ validInContext t' Γ
          then (compareHnfs t (strengthen t')) else hnfError t t''
        t'' → hnfError t t''
      {-# CATCHALL #-}
      compareHnfs t t' = hnfError t t'

  checkβη : AnnTerm → AnnTerm → M ⊤
  checkβη t t' = checkβηPure (Erase t) (Erase t')

{-# TERMINATING #-}
synthType synthType' :
  {{_ : Monad M}} {{_ : MonadExcept M String}} → Context → AnnTerm → M AnnTerm

synthType Γ t =
  appendIfError (synthType' Γ t) $
    "\n\nWhile synthesizing type for" <+> shortenString 1000 (show t) <+> "in context:\n" + show {{Context-Show}} Γ

synthType' Γ (Var-A x) =
  maybeToError
    (typeOfDef <$> lookupInContext x Γ)
    ("Lookup failed:" <+> show x <+> "in context" <+> show {{Context-Show}} Γ)
synthType' Γ (Sort-A Ast) = return □
synthType' Γ (Sort-A Sq) = throwError "Cannot synthesize type for the superkind"

synthType' Γ (Const-A CharT) = return ⋆

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
    { (Sort-A Ast) → return $ Eq-A t t
    ; _ → throwError "Equality type does not have the right type. Is this a bug?" }

synthType' Γ (Delta-A t t₁) = do
  T ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (Eq-A u u₁) → do
      catchError
        (pureTermBeq (normalizePure Γ $ Erase u) (Lam-P "" $ Lam-P "" $ BoundVar 1) >>
         pureTermBeq (normalizePure Γ $ Erase u₁) (Lam-P "" $ Lam-P "" $ BoundVar 0))
        (λ e → throwError $
          "This equality cannot be used for the delta term:" <+> show u
          <+> "=" <+> show u₁ + "\nError:" <+> e)
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
        (λ e → throwError ("Type mismatch in application, the type of" <+> show t₁
          <+> ":" <+> show T₁ +  " is not βη-equivalent to" <+> show u + "\nError:" <+> e))
      return $ subst u₁ t₁
    ; v → throwError $
      "The left term in an application needs to have a pi type, while it has type" <+> show v }

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
        + show v + "\nTest:" <+> show T }

synthType' Γ (Rho-A t t₁ t₂) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₂
  case (hnfNorm Γ T) of λ
    { (Eq-A u u₁) → do
      catchError (checkβη Γ (subst t₁ u₁) T₁)
        (λ e → throwError $ "Type mismatch in rho:" <+> show (subst t₁ u₁)
          <+> "should be βη-equivalent to the synthesized type of" <+> show t₂ <+> ": "
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
        { (Sort-A Ast) → return ⋆
        ; v → throwError $
          "The type family in forall should have type star, while it has type "
          + show v <+> "(" + show t₁ + ")\nContext:" <+> show {{Context-Show}} Γ' }
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
          "The type family in pi should have type star or square, while it has type" <+> show v }
    ; _ → throwError "The type of the parameter type in pi should be star or square" }

synthType' Γ (Iota-A _ t t₁) = do
  u ← synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-A Ast) → do
      let Γ' = pushVar t Γ
      u₁ ← synthType Γ' t₁
      case (hnfNorm Γ' u₁) of λ
        { (Sort-A Ast) → return ⋆
        ; _ → throwError "The type family in iota should have type star"}
    ; _ → throwError "The type of the parameter type in iota should be star" }

synthType' Γ (Lam-A n t t₁) = do
  synthType Γ t
  u ← synthType (pushVar t Γ) t₁
  return (Pi-A n t u)

synthType' Γ (LamE-A n t t₁) =
  if checkFree (Bound 0) (Erase t₁)
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
        + show (subst t₂ t) <+> "should be βη-equivalent to the synthesized type "
        + show u₁ + "\n" + e))
  let res = Iota-A "" u t₂
  u₂ ← synthType Γ res
  case (hnfNorm Γ u₂) of λ
    { (Sort-A Ast) → return res
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
      then return ⋆
      else throwError
        ("The right term in the equality type needs to be valid in the context:" <+> show x₁)
    else throwError
      ("The left term in the equality type needs to be valid in the context:" <+> show x)

synthType' Γ (M-A t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Sort-A Ast) → return ⋆
    ; _ → throwError "The term M is applied to should have type ∗"}

synthType' Γ (Mu-A t t₁) = do
  T ← synthType Γ t
  T' ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (M-A u) →
      case (hnfNorm Γ T') of λ
        { (Pi-A _ v v₁) → do
          T'' ← if checkFree (Bound 0) (Erase v₁)
            then throwError ("Index 0 is not allowed to appear in" <+> show v₁)
            else synthType (pushVar v Γ) v₁
          case (hnfNorm Γ T'') of λ
            { (Sort-A ∗) →
              case (hnfNorm Γ v₁) of λ
                { (M-A v₂) →
                  appendIfError
                    (checkβη Γ u v)
                    "The types in μ need to be compatible" >> return (M-A $ strengthen v₂)
                ; _ → throwError
                  "The second term in a μ needs to have a Pi type that maps to 'M t' for some 't'" }
            ; _ → throwError "The second term in a μ needs to have a non-dependent Pi type" }
        ; _ → throwError "The second term in a μ needs to have a Pi type" }
    ; _ → throwError "The first term in a μ needs to have type 'M t' for some 't'" }

synthType' Γ (Epsilon-A t) = M-A <$> synthType Γ t

synthType' Γ (Ev-A m t) = do
  T ← traversePrimMetaArgs (synthType Γ) t
  appendIfError
    (primMetaArgsSequence $ primMetaArgsZipWith (checkβη Γ) T $ primMetaS m)
    ("The arguments for primitive" <+> show m <+> "have incorrect types!")
  return $ M-A $ primMetaT m t

synthType' Γ (Gamma-A t t₁) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (M-A u) → do
      appendIfError (checkβη Γ T₁ (Pi-A "" (FreeVar "init$err") (weakenBy 1 $ M-A u)))
        ("The second term supplied to CatchErr has type" <+> show T₁ +
         ", while it should have type 'init$err → M" <+> show u)
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
