--------------------------------------------------------------------------------
-- This file provides the data structures and functions for the theory of
-- cedille core extended with the constructs for metaprogramming.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Theory.TypeChecking where

import Data.Product

open import Data.HSTrie
open import Class.Map
open import Class.Monad.Except
open import Data.Word using (toℕ; fromℕ)
open import Monads.Except

open import Prelude
open import Prelude.Nat

open import Theory.Names public
open import Theory.TermLike public
open import Theory.PrimMeta public
open import Theory.Terms hiding (PureTerm) public
import Theory.NBE as NBE
open import Theory.Context public
open import Theory.Normalisation public
open import Theory.NBE using (genExtra)

module _ {a b : Bool} where
  open Types (Term-TermLike {a} {b}) public

PureTerm : Set
PureTerm = Theory.Terms.PureTerm false

private
  variable
    A B C : Set
    M : Set → Set

  {-# TERMINATING #-}
  checkFree : Name → PureTerm → Bool
  checkFree = helper 0
    where
      helper : 𝕀 → Name → PureTerm → Bool
      helper k n (Var-T (Bound x)) = case n of λ where
        (Bound x₁) → x ≣ (k +𝕀 x₁)
        (Free x₁) → false
      helper k n (Var-T (Free x)) = case n of λ where
        (Bound x₁) → false
        (Free x₁) → x ≣ x₁
      helper k n (Sort-T x) = false
      helper k n (Const-T x) = false
      helper k n (App t t₁) = helper k n t ∧ helper k n t₁
      helper k n (Lam-P _ t) = helper (suc𝕀 k) n t
      helper k n (Pi _ t t₁) = helper k n t ∧ helper (suc𝕀 k) n t₁
      helper k n (All _ t t₁) = helper k n t ∧ helper (suc𝕀 k) n t₁
      helper k n (Iota _ t t₁) = helper k n t ∧ helper (suc𝕀 k) n t₁
      helper k n (Eq-T t t₁) = helper k n t ∧ helper k n t₁
      helper k n (M-T t) = helper k n t
      helper k n (Mu t t₁) = helper k n t ∧ helper k n t₁
      helper k n (Epsilon t) = helper k n t
      helper k n (Gamma t t₁) = helper k n t ∧ helper k n t₁
      helper k n (Ev m t) = primMetaArgsAnd $ mapPrimMetaArgs (helper k n) t
      helper k n (Char-T c) = false
      helper k n (CharEq t t₁) = helper k n t ∧ helper k n t₁

insertInGlobalContext : GlobalName → Def → GlobalContext → String ⊎ GlobalContext
insertInGlobalContext n d Γ =
  if is-just $ lookup n Γ
    then inj₁ ("The name" <+> n <+> "is already defined!")
    else (inj₂ $ insert n (toEfficientDef d Γ) Γ)
  where
    toEfficientDef : Def → GlobalContext → Def
    toEfficientDef d@(≔ x) Γ = record d { extra = just $ genExtra (globalToContext Γ) $ Erase x }
    toEfficientDef d Γ = d

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
  pureTermBeq (Var-T x) (Var-T x₁) = beqMonadHelper x x₁ "Name"
  pureTermBeq (Sort-T x) (Sort-T x₁) = beqMonadHelper x x₁ "Sort"
  pureTermBeq (Const-T x) (Const-T x₁) = beqMonadHelper x x₁ "Const"
  pureTermBeq (App t t₁) (App x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Lam-P _ t) (Lam-P _ t₁) = pureTermBeq t t₁
  pureTermBeq (Pi _ t t₁) (Pi _ x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (All _ t t₁) (All _ x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Iota _ t t₁) (Iota _ x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Eq-T t t₁) (Eq-T x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (M-T t) (M-T x) = pureTermBeq x t
  pureTermBeq (Mu t t₁) (Mu x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Epsilon t) (Epsilon x) = pureTermBeq t x
  pureTermBeq (Gamma t t₁) (Gamma x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Ev m t) (Ev m' x) with m ≟ m'
  ... | yes refl = void $ primMetaArgsSequence $ primMetaArgsZipWith pureTermBeq t x
  ... | no  _    = throwError $ show m <+> "and" <+> show m' <+> "aren't equal!"
  pureTermBeq (Char-T c) (Char-T c') = beqMonadHelper c c' "Char"
  pureTermBeq (CharEq t t₁) (CharEq x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
  {-# CATCHALL #-}
  pureTermBeq t t' =
    throwError $ "The terms" <+> show t <+> "and" <+> show t' <+> "aren't equal!"

module _ {{_ : Monad M}} {{_ : MonadExcept M String}} (Γ : Context) where
  compareNames : PureTerm → PureTerm → M ⊤
  compareNames (Var-T x) (Var-T x₁) =
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
      compareHnfs (Var-T x) (Var-T x₁) = beqMonadHelper x x₁ "Name"
      compareHnfs (Sort-T x) (Sort-T x₁) = beqMonadHelper x x₁ "Sort-T"
      compareHnfs (Const-T x) (Const-T x₁) = beqMonadHelper x x₁ "Const"
      compareHnfs (App t t₁) (App x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Lam-P _ t) (Lam-P _ t₁) = checkβηPure t t₁
      compareHnfs (Pi _ t t₁) (Pi _ x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (All _ t t₁) (All _ x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Iota _ t t₁) (Iota _ x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Eq-T t t₁) (Eq-T x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (M-T t) (M-T x) = checkβηPure x t
      compareHnfs (Mu t t₁) (Mu x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Epsilon t) (Epsilon x) = checkβηPure t x
      compareHnfs (Gamma t t₁) (Gamma x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs t@(Ev m x) t'@(Ev m' x') with m ≟ m'
      ... | yes refl = void $ primMetaArgsSequence $ primMetaArgsZipWith checkβηPure x x'
      ... | no  _    = hnfError t t'
      compareHnfs (Char-T c) (Char-T c') = beqMonadHelper c c' "Char"
      compareHnfs (CharEq t t₁) (CharEq x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Lam-P _ t) t₁ = case normalizePure Γ t of λ where
        t''@(App t' (Var-T (Bound i))) → if i ≣ 0 ∧ validInContext t' Γ
          then (compareHnfs (strengthen t') t₁) else hnfError t'' t₁
        t'' → hnfError t'' t₁
      compareHnfs t (Lam-P _ t₁) = case normalizePure Γ t₁ of λ where
        t''@(App t' (Var-T (Bound i))) → if i ≣ 0 ∧ validInContext t' Γ
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

synthType' Γ (Var-T x) =
  maybeToError
    (lookupTypeInContext x Γ)
    ("Lookup failed:" <+> show x <+> "in context" <+> show {{Context-Show}} Γ)
synthType' Γ (Sort-T Ast) = return □
synthType' Γ (Sort-T Sq) = throwError "Cannot synthesize type for the superkind"

synthType' Γ (Const-T CharT) = return ⋆

synthType' Γ (Pr1 t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Iota _ u u₁) → return u
    ; _ → throwError "Term does not normalize to an iota term" }

synthType' Γ (Pr2 t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Iota _ u u₁) → return $ subst u₁ (Pr1 t)
    ; _ → throwError "Term does not normalize to an iota term" }

synthType' Γ (Beta t t₁) = do
  T ← synthType Γ (Eq-T t t)
  case (hnfNorm Γ T) of λ
    { (Sort-T Ast) → return $ Eq-T t t
    ; _ → throwError "Equality type does not have the right type. Is this a bug?" }

synthType' Γ (Delta t t₁) = do
  T ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (Eq-T u u₁) → do
      catchError
        (pureTermBeq (normalizePure Γ $ Erase u) (Lam-P "" $ Lam-P "" $ BoundVar 1) >>
         pureTermBeq (normalizePure Γ $ Erase u₁) (Lam-P "" $ Lam-P "" $ BoundVar 0))
        (λ e → throwError $
          "This equality cannot be used for the delta term:" <+> show u
          <+> "=" <+> show u₁ + "\nError:" <+> e)
      return t
    ; _ → throwError "The second argument of a delta needs to be of an eq type" }

synthType' Γ (Sigma t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Eq-T u u₁) → return $ Eq-T u₁ u
    ; _ → throwError "Sigma needs an inhabitant of an eq type as argument" }

synthType' Γ (App t t₁) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (Pi _ u u₁) → do
      catchError
        (checkβη Γ T₁ u)
        (λ e → throwError ("Type mismatch in application, the type of" <+> show t₁
          <+> ":" <+> show T₁ +  " is not βη-equivalent to" <+> show u + "\nError:" <+> e))
      return $ subst u₁ t₁
    ; v → throwError $
      "The left term in an application needs to have a pi type, while it has type" <+> show v }

synthType' Γ (AppE t t₁) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (All _ u u₁) → do
      catchError (checkβη Γ u T₁)
        (λ e → throwError
          ("Type mismatch in erased application, the following types are not βη-equivalent:\n"
            + show u + "\n" + show T₁ + "\nError:\n" + e))
      return $ subst u₁ t₁
    ; v → throwError $
      "The left term in an erased application needs to have a forall type, while it has type "
        + show v + "\nTest:" <+> show T }

synthType' Γ (Rho t t₁ t₂) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₂
  case (hnfNorm Γ T) of λ
    { (Eq-T u u₁) → do
      catchError (checkβη Γ (subst t₁ u₁) T₁)
        (λ e → throwError $ "Type mismatch in rho:" <+> show (subst t₁ u₁)
          <+> "should be βη-equivalent to the synthesized type of" <+> show t₂ <+> ": "
          + show T₁ + "\nError:\n" + e)
      return $ subst t₁ u
    ; _ → throwError "The type of the first argument of a rho needs to be an equality" }

synthType' Γ (All n t t₁) = do
  u ← synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-T s) → do
      let Γ' = pushType Γ (n , t)
      u₁ ← synthType Γ' t₁
      case (hnfNorm Γ' u₁) of λ
        { (Sort-T Ast) → return ⋆
        ; v → throwError $
          "The type family in forall should have type star, while it has type "
          + show v <+> "(" + show t₁ + ")\nContext:" <+> show {{Context-Show}} Γ' }
    ; _ → throwError "The type of the parameter type in forall should be star or square" }

synthType' Γ (Pi n t t₁) = do
  u ← synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-T s) → do
      let Γ' = pushType Γ (n , t)
      u₁ ← synthType Γ' t₁
      case (hnfNorm Γ u₁) of λ
        { (Sort-T s') → return $ Sort-T s'
        ; v → throwError $
          "The type family in pi should have type star or square, while it has type" <+> show v }
    ; _ → throwError "The type of the parameter type in pi should be star or square" }

synthType' Γ (Iota n t t₁) = do
  u ← synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-T Ast) → do
      let Γ' = pushType Γ (n , t)
      u₁ ← synthType Γ' t₁
      case (hnfNorm Γ' u₁) of λ
        { (Sort-T Ast) → return ⋆
        ; _ → throwError "The type family in iota should have type star"}
    ; _ → throwError "The type of the parameter type in iota should be star" }

synthType' Γ (Lam-A n t t₁) = do
  synthType Γ t
  u ← synthType (pushType Γ (n , t)) t₁
  return (Pi n t u)

synthType' Γ (LamE n t t₁) =
  if checkFree (Bound 0) (Erase t₁)
    then throwError "Erased arguments cannot appear bound in a term"
    else do
      synthType Γ t
      u ← synthType (pushType Γ (n , t)) t₁
      return $ All n t u

synthType' Γ (Pair t t₁ t₂) = do
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
  let res = Iota "" u t₂
  u₂ ← synthType Γ res
  case (hnfNorm Γ u₂) of λ
    { (Sort-T Ast) → return res
    ; _ → throwError
      "The resulting iota type of the dependent intersection doesn't have type star. Is this a Bug?" }

synthType' Γ (Phi t t₁ t₂) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Eq-T u u₁) → do
      catchError
        (checkβη Γ t₁ u >> checkβη Γ t₂ u₁)
        (λ e → throwError $
          "The arguments to phi are not equivalent to the sides of the equality. Error:\n" + e)
      synthType Γ t₁
    ; _ → throwError "The first argument to phi should be of an equality type" }

synthType' Γ (Eq-T x x₁) =
  if validInContext (Erase x) Γ
    then if validInContext (Erase x₁) Γ
      then return ⋆
      else throwError
        ("The right term in the equality type needs to be valid in the context:" <+> show x₁)
    else throwError
      ("The left term in the equality type needs to be valid in the context:" <+> show x)

synthType' Γ (M-T t) = do
  T ← synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Sort-T Ast) → return ⋆
    ; _ → throwError "The term M is applied to should have type ∗"}

synthType' Γ (Mu t t₁) = do
  T ← synthType Γ t
  T' ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (M-T u) →
      case (hnfNorm Γ T') of λ
        { (Pi _ v v₁) → do
          T'' ← if checkFree (Bound 0) (Erase v₁)
            then throwError ("Index 0 is not allowed to appear in" <+> show v₁)
            else synthType (pushType Γ ("_" , v)) v₁
          case (hnfNorm Γ T'') of λ
            { (Sort-T ∗) →
              case (hnfNorm Γ v₁) of λ
                { (M-T v₂) →
                  appendIfError
                    (checkβη Γ u v)
                    "The types in μ need to be compatible" >> return (M-T $ strengthen v₂)
                ; _ → throwError
                  "The second term in a μ needs to have a Pi type that maps to 'M t' for some 't'" }
            ; _ → throwError "The second term in a μ needs to have a non-dependent Pi type" }
        ; _ → throwError "The second term in a μ needs to have a Pi type" }
    ; t → throwError ("The first term in a μ needs to have type 'M t' for some 't'. It has type " <+> show t) }

synthType' Γ (Epsilon t) = M-T <$> synthType Γ t

synthType' Γ (Ev m t) = do
  T ← traversePrimMetaArgs (synthType Γ) t
  appendIfError
    (primMetaArgsSequence $ primMetaArgsZipWith (checkβη Γ) T $ primMetaS m)
    ("The arguments for primitive" <+> show m <+> "have incorrect types!")
  return $ M-T $ primMetaT m t

synthType' Γ (Gamma t t₁) = do
  T ← synthType Γ t
  T₁ ← synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (M-T u) → do
      appendIfError (checkβη Γ T₁ (Pi "" (FreeVar "init$err") (weakenBy 1 $ M-T u)))
        ("The second term supplied to CatchErr has type" <+> show T₁ +
         ", while it should have type 'init$err → M" <+> show u)
      return $ M-T u
    ; _ → throwError "The first term in CatchErr needs to have type 'M t' for some 't'" }

synthType' Γ (Char-T c) = return (Const-T CharT)
synthType' Γ (CharEq t t') = do
  T ← synthType Γ t
  T' ← synthType Γ t'
  case (hnfNorm Γ T) of λ
    { (Const-T CharT) → case (hnfNorm Γ T') of λ
      { (Const-T CharT) → return $ FreeVar "Bool"
      ; _ → throwError "The second term in CharEq needs to have type Char" }
    ; _ → throwError "The first term in CharEq needs to have type Char" }
