--------------------------------------------------------------------------------
-- This file provides the data structures and functions for the theory of
-- cedille core extended with the constructs for metaprogramming.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Theory.TypeChecking where

import Data.Product

open import Data.HSTrie
open import Class.Map
open import Class.Monad.Reader
open import Class.Monad.Except
open import Data.Word using (toℕ; fromℕ)
open import Data.Sum using (map₁)
open import Monads.Except
open import Monads.ExceptT

open import Prelude hiding (map₁)
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

-- instance
--   _ = ExceptT-Monad
--   _ = ExceptT-MonadExcept

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

TCErrorMsg : Set
TCErrorMsg = List (String ⊎ AnnTerm)

TCError : Set
TCError = AnnTerm × Context × TCErrorMsg

record IsTCErrorMsg (A : Set) : Set where
  field toTCErrorMsg : A → String ⊎ AnnTerm

open IsTCErrorMsg ⦃...⦄

instance
  IsTCErrorMsg-String : IsTCErrorMsg String
  IsTCErrorMsg-String .toTCErrorMsg = inj₁

  IsTCErrorMsg-AnnTerm : IsTCErrorMsg AnnTerm
  IsTCErrorMsg-AnnTerm .toTCErrorMsg = inj₂

infixr 0 _∷ᵗ_
_∷ᵗ_ : A → ⦃ IsTCErrorMsg A ⦄ → TCErrorMsg → TCErrorMsg
a ∷ᵗ es = toTCErrorMsg a ∷ es

instance
  Show-TCError : Show TCError
  Show-TCError .show (tm , Γ@(_ , Γ') , msg) = let showTerm = showTermCtx (map proj₁ Γ') in
    foldl _<+>_ "" (map Data.Sum.[ id , showTerm ] msg)
    + "\n\nWhile synthesizing type for" <+> showTerm tm
    <+> "in context:\n" + show {{Context-Show}} Γ + "\n\n"

insertInGlobalContext : GlobalName → Def → GlobalContext → String ⊎ GlobalContext
insertInGlobalContext n d Γ =
  if is-just $ lookup n Γ
    then inj₁ ("The name" <+> n <+> "is already defined!")
    else (inj₂ $ insert n (toEfficientDef d Γ) Γ)
  where
    toEfficientDef : Def → GlobalContext → Def
    toEfficientDef d@(≔ x) Γ = record d { extra = just $ genExtra (globalToContext Γ) $ Erase x }
    toEfficientDef d Γ = d

module StringErr ⦃ _ : Monad M ⦄ ⦃ _ : MonadExcept M String ⦄ where

  beqMonadHelper : ⦃ _ : EqB A ⦄ ⦃ _ : Show A ⦄ → A → A → String → M ⊤
  beqMonadHelper a a' s =
    if a ≣ a'
      then return tt
      else throwError (s <+> show a <+> "isn't equal to" <+> s <+> show a')

  {-# TERMINATING #-}
  pureTermBeq : PureTerm → PureTerm → M ⊤
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

  module _ (Γ : Context) where
    compareNames : PureTerm → PureTerm → M ⊤
    compareNames (Var-T x) (Var-T x₁) =
      if x ≣ x₁
        then return tt
        else throwError "Names not equal! If you see this message, this is a bug!"
    {-# CATCHALL #-}
    compareNames _ _ = throwError "Terms are not names! If you see this message, this is a bug!"

    {-# NON_TERMINATING #-}
    checkβηPure : PureTerm → PureTerm → M ⊤
    checkβηPure t t' = appendIfError
      (tryElse (compareNames t t') $
      compareHnfs (hnfNormPure Γ t) (hnfNormPure Γ t'))
      ("\n\nWhile checking equality of" <+> show t <+> "and" <+> show t')
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

module _ ⦃ _ : Monad M ⦄ ⦃ _ : MonadReader M Context ⦄ ⦃ _ : MonadExcept M TCError ⦄ where

  open StringErr {M = ExceptT M String} ⦃ ExceptT-Monad ⦄ ⦃ ExceptT-MonadExcept ⦄

  throwErrorCtx : AnnTerm → TCErrorMsg → M A
  throwErrorCtx tm msg = do
    Γ ← ask
    throwError (tm , Γ , msg)

  appendIfError' : M (String ⊎ A) → AnnTerm → TCErrorMsg → M A
  appendIfError' x tm msg = do
    (inj₁ e) ← x
      where (inj₂ a) → return a
    throwErrorCtx tm (msg + ("\nReason:" ∷ᵗ e ∷ᵗ []))

  throwError1 : AnnTerm → String → M A
  throwError1 tm s = throwErrorCtx tm (s ∷ᵗ [])

  hnfNormM : AnnTerm → M AnnTerm
  hnfNormM t = do
    Γ ← ask
    return $ hnfNorm Γ t

  {-# TERMINATING #-}
  synthType' : AnnTerm → M AnnTerm

  synthType' tm@(Var-T x) = do
    Γ ← ask
    case (lookupTypeInContext x Γ) of λ
      { (just T) → return T
      ; nothing → throwErrorCtx tm
        (("Lookup failed:" <+> show x + "\nIn context:" <+> show {{Context-Show}} Γ) ∷ᵗ []) }

  synthType' tm@(Sort-T Ast) = return □
  synthType' tm@(Sort-T Sq) = throwError1 tm "Cannot synthesize type for the kind □"

  synthType' tm@(Const-T CharT) = return ⋆

  synthType' tm@(Pr1 t) = do
    T ← synthType' t
    (Iota _ u u₁) ← hnfNormM T
      where _ → throwError1 tm "Term does not normalize to an iota term"
    return u

  synthType' tm@(Pr2 t) = do
    T ← synthType' t
    (Iota _ u u₁) ← hnfNormM T
      where _ → throwError1 tm "Term does not normalize to an iota term"
    return $ subst u₁ (Pr1 t)

  synthType' tm@(Beta t t₁) = do
    T ← synthType' (Eq-T t t)
    (Sort-T Ast) ← hnfNormM T
      where _ → throwError1 tm "Equality type does not have the right type. Is this a bug?"
    return $ Eq-T t t

  synthType' tm@(Delta t t₁) = do
    Γ ← ask
    T ← synthType' t₁
    (Eq-T u u₁) ← hnfNormM T
      where _ → throwError1 tm "The second argument of a delta needs to be of an eq type"
    appendIfError'
      (pureTermBeq (normalizePure Γ $ Erase u) (Lam-P "" $ Lam-P "" $ BoundVar 1) >>
       pureTermBeq (normalizePure Γ $ Erase u₁) (Lam-P "" $ Lam-P "" $ BoundVar 0))
      tm ("This equality cannot be used for the delta term:" ∷ᵗ u ∷ᵗ "=" ∷ᵗ u₁ ∷ᵗ [])
    return t

  synthType' tm@(Sigma t) = do
    T ← synthType' t
    (Eq-T u u₁) ← hnfNormM T
      where _ → throwError1 tm "Sigma needs an inhabitant of an eq type as argument"
    return $ Eq-T u₁ u

  synthType' tm@(App t t₁) = do
    Γ ← ask
    T ← synthType' t
    T₁ ← synthType' t₁
    (Pi _ u u₁) ← hnfNormM T
      where v → throwErrorCtx tm $
             "The left term in an application needs to have a pi type, while it has type" ∷ᵗ v ∷ᵗ []
    appendIfError' (checkβη Γ T₁ u) tm
      ("Type mismatch in application:" ∷ᵗ App t t₁ ∷ᵗ "\nThe type of RHS," ∷ᵗ
       T₁ ∷ᵗ "is not βη-equivalent to" ∷ᵗ u ∷ᵗ [])
    return $ subst u₁ t₁

  synthType' tm@(AppE t t₁) = do
    Γ ← ask
    T ← synthType' t
    T₁ ← synthType' t₁
    (All _ u u₁) ← hnfNormM T
      where v → throwErrorCtx tm $
             "The left term in an erased application needs to have a forall type, while it has type" ∷ᵗ v ∷ᵗ []
    appendIfError' (checkβη Γ u T₁) tm
      ("Type mismatch in application:" ∷ᵗ AppE t t₁ ∷ᵗ "\nThe type of RHS," ∷ᵗ
       T₁ ∷ᵗ "is not βη-equivalent to" ∷ᵗ u ∷ᵗ [])
    return $ subst u₁ t₁

  synthType' tm@(Rho t t₁ t₂) = do
    Γ ← ask
    T ← synthType' t
    T₁ ← synthType' t₂
    (Eq-T u u₁) ← hnfNormM T
      where _ → throwError1 tm "The type of the first argument of a rho needs to be an equality"
    appendIfError' (checkβη Γ (subst t₁ u₁) T₁) tm
      ("Type mismatch in rho:" ∷ᵗ subst t₁ u₁ ∷ᵗ "should be βη-equivalent to the type of" ∷ᵗ
       t₂ ∷ᵗ ":" ∷ᵗ T₁ ∷ᵗ [])
    return $ subst t₁ u

  synthType' tm@(All n t t₁) = do
    Γ ← ask
    u ← synthType' t
    (Sort-T s) ← hnfNormM u
      where v → throwErrorCtx tm $
             "The type of the parameter type in forall should be a sort, but it has type" ∷ᵗ v ∷ᵗ []
    let Γ' = pushType Γ (n , t)
    u₁ ← local (λ _ → Γ') $ synthType' t₁
    case (hnfNorm Γ' u₁) of λ
      { (Sort-T Ast) → return ⋆
      ; v → throwErrorCtx tm $
        "The type family in forall should have type ⋆, but it has type"
        ∷ᵗ v ∷ᵗ "\nContext:" <+> show {{Context-Show}} Γ' ∷ᵗ [] }

  synthType' tm@(Pi n t t₁) = do
    Γ ← ask
    u ← synthType' t
    (Sort-T s) ← hnfNormM u
      where v → throwErrorCtx tm $
             "The type of the parameter type in pi should be a sort, but it has type" ∷ᵗ v ∷ᵗ []
    let Γ' = pushType Γ (n , t)
    u₁ ← local (λ _ → Γ') $ synthType' t₁
    (Sort-T s') ← hnfNormM u₁
      where v → throwErrorCtx tm $
             "The type family in pi should be a sort, but it has type"
             ∷ᵗ v ∷ᵗ "\nContext:" <+> show {{Context-Show}} Γ' ∷ᵗ []
    return $ Sort-T s'

  synthType' tm@(Iota n t t₁) = do
    Γ ← ask
    u ← synthType' t
    (Sort-T Ast) ← hnfNormM u
      where v → throwErrorCtx tm $
             "The type of the parameter type in iota should be ⋆, but it has type" ∷ᵗ v ∷ᵗ []
    let Γ' = pushType Γ (n , t)
    u₁ ← local (λ _ → Γ') $ synthType' t₁
    case (hnfNorm Γ' u₁) of λ
      { (Sort-T Ast) → return ⋆
      ; v → throwErrorCtx tm $
        "The type family in iota should have type ⋆, but it has type"
        ∷ᵗ v ∷ᵗ "\nContext:" <+> show {{Context-Show}} Γ' ∷ᵗ [] }

  synthType' tm@(Lam-A n t t₁) = do
    synthType' t
    u ← local (flip pushType (n , t)) $ synthType' t₁
    return (Pi n t u)

  synthType' tm@(LamE n t t₁) =
    if checkFree (Bound 0) (Erase t₁)
      then throwErrorCtx tm $ "Erased argument" ∷ᵗ (BoundVar 0) ∷ᵗ "cannot appear in a relevant position" ∷ᵗ []
      else do
        synthType' t
        u ← local (flip pushType (n , t)) $ synthType' t₁
        return $ All n t u

  synthType' tm@(Pair t t₁ t₂) = do
    Γ ← ask
    appendIfError' (checkβη Γ t t₁) tm
      ("The terms in dependent intersection introduction have to be βη-equivalent!" ∷ᵗ [])
    u ← synthType' t
    u₁ ← synthType' t₁
    appendIfError'
      (checkβη Γ (subst t₂ t) u₁) tm
      ("Type mismatch in the second argument of dependent intersection:" ∷ᵗ
       (subst t₂ t) ∷ᵗ "should be βη-equivalent to the type" ∷ᵗ u₁ ∷ᵗ [])
    let res = Iota "" u t₂
    u₂ ← synthType' res
    (Sort-T Ast) ← hnfNormM u₂
      where _ → throwError1 tm
             "The resulting iota type of the dependent intersection doesn't have type star. Is this a Bug?"
    return res

  synthType' tm@(Phi t t₁ t₂) = do
    Γ ← ask
    T ← synthType' t
    (Eq-T u u₁) ← hnfNormM T
      where v → throwErrorCtx tm $
             "The first argument to phi should be of an equality type, but it has type" ∷ᵗ v ∷ᵗ []
    appendIfError' (checkβη Γ t₁ u >> checkβη Γ t₂ u₁) tm
      ("The arguments to phi are not equivalent to the sides of the equality." ∷ᵗ [])
    synthType' t₁

  synthType' tm@(Eq-T x x₁) = do
    Γ ← ask
    if validInContext (Erase x) Γ
      then if validInContext (Erase x₁) Γ
        then return ⋆
        else throwErrorCtx tm
          ("The right term in the equality type needs to be valid in the context:" ∷ᵗ x₁ ∷ᵗ [])
      else throwErrorCtx tm
        ("The left term in the equality type needs to be valid in the context:" ∷ᵗ x ∷ᵗ [])

  synthType' tm@(M-T t) = do
    T ← synthType' t
    (Sort-T Ast) ← hnfNormM T
      where v → throwErrorCtx tm $
             "M can only be applied to terms of type ∗, but it was applied to a term of type" ∷ᵗ v ∷ᵗ []
    return ⋆

  synthType' tm@(Mu t t₁) = do
    Γ ← ask
    T ← synthType' t
    T' ← synthType' t₁
    (M-T u) ← hnfNormM T
      where t → throwErrorCtx tm $
             "The first term in a μ needs to have type 'M t' for some 't'. It has type" ∷ᵗ t ∷ᵗ []
    (Pi _ v v₁) ← hnfNormM T'
      where t → throwErrorCtx tm $
             "The second term in a μ needs to have a Pi type, but it has type" ∷ᵗ t ∷ᵗ []
    if checkFree (Bound 0) (Erase v₁)
      then throwErrorCtx tm
        ("The type of the second argument to μ needs to be non-dependent, but it had type"
        ∷ᵗ T' ∷ᵗ [])
      else (local (flip pushType ("_" , v)) $ synthType' v₁)
    (M-T v₂) ← hnfNormM v₁
      where t → throwErrorCtx tm $
             "The second term in a μ needs to have a Pi type that maps to 'M t' for some 't'."
             ∷ᵗ "It has type" ∷ᵗ t ∷ᵗ []
    appendIfError' (checkβη Γ u v) tm
      ("The types in μ need to be compatible" ∷ᵗ [])
    return (M-T $ strengthen v₂)

  synthType' tm@(Epsilon t) = M-T <$> synthType' t

  synthType' tm@(Ev m t) = do
    Γ ← ask
    T ← traversePrimMetaArgs synthType' t
    primMetaArgsSequence $ primMetaArgsZipWith (λ t₁ t₂ → appendIfError' (checkβη Γ t₁ t₂) tm
        ("The arguments for primitive" <+> show m <+> "have incorrect types!" ∷ᵗ []))
      T (primMetaS m)
    return $ M-T $ primMetaT m t

  synthType' tm@(Gamma t t₁) = do
    Γ ← ask
    T ← synthType' t
    T₁ ← synthType' t₁
    (M-T u) ← hnfNormM T
      where t → throwErrorCtx tm $
             "The first term in CatchErr needs to have type 'M t' for some 't', but it has type" ∷ᵗ t ∷ᵗ []
    appendIfError' (checkβη Γ T₁ (Pi "" (FreeVar "init$err") (weakenBy 1 $ M-T u))) tm
      ("The second term supplied to CatchErr has type" ∷ᵗ T₁ ∷ᵗ
       ", while it should have type 'init$err → M" ∷ᵗ u ∷ᵗ [])
    return $ M-T u

  synthType' tm@(Char-T c) = return (Const-T CharT)
  synthType' tm@(CharEq t t') = do
    T ← synthType' t
    T' ← synthType' t'
    (Const-T CharT) ← hnfNormM T
      where v → throwErrorCtx tm $
             "The first term in CharEq needs to have type Char, but it has type" ∷ᵗ v ∷ᵗ []
    (Const-T CharT) ← hnfNormM T'
      where v → throwErrorCtx tm $
             "The second term in CharEq needs to have type Char, but it has type" ∷ᵗ v ∷ᵗ []
    return $ FreeVar "Bool"

synthType : ⦃ _ : Monad M ⦄ ⦃ _ : MonadExcept M String ⦄ → Context → AnnTerm → M AnnTerm
synthType Γ t = do
  (inj₂ t) ← map₁ (show ⦃ Show-TCError ⦄) <$>
    synthType' ⦃ ExceptT-Monad ⦃ Monad-ReaderT ⦄ ⦄
               ⦃ ExceptT-MonadReader ⦃ Monad-ReaderT ⦄ ⦃ MonadReader-ReaderT ⦄ ⦄
               ⦃ ExceptT-MonadExcept ⦃ Monad-ReaderT ⦄ ⦄
               t Γ
    where (inj₁ msg) → throwError msg
  return t
