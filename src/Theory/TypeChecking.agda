--------------------------------------------------------------------------------
-- This file provides the data structures and functions for the theory of
-- cedille core extended with the constructs for metaprogramming.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Theory.TypeChecking where

open import Class.Map
open import Class.Monad.Except
open import Class.Monad.Reader
open import Data.HSTrie
open import Data.Sum using (map₁)
open import Monads.ExceptT

open import Prelude hiding (map₁)
open import Prelude.Nat

open import Theory.Context public
open import Theory.Evaluation public
open import Theory.NBE using (genExtra)
import Theory.Normalisation as N
open import Theory.Terms hiding (PureTerm) public

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
      helper k n (BoundVar x)  = case n of λ where
        (Bound x₁) → x ≣ (k +𝕀 x₁)
        (Free x₁) → false
      helper k n (FreeVar x)   = case n of λ where
        (Bound x₁) → false
        (Free x₁) → x ≣ x₁
      helper k n (Sort-T x)    = false
      helper k n (Const-T x)   = false
      helper k n (App b t t₁)  = helper k n t ∧ helper k n t₁
      helper k n (Lam-P _ _ t) = helper (suc𝕀 k) n t
      helper k n (Pi _ _ t t₁) = helper k n t ∧ helper (suc𝕀 k) n t₁
      helper k n (Iota _ t t₁) = helper k n t ∧ helper (suc𝕀 k) n t₁
      helper k n (Eq-T t t₁)   = helper k n t ∧ helper k n t₁
      helper k n (M-T t)       = helper k n t
      helper k n (Mu t t₁)     = helper k n t ∧ helper k n t₁
      helper k n (Epsilon t)   = helper k n t
      helper k n (Ev m t)      = primMetaArgsAnd $ mapPrimMetaArgs (helper k n) t

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

  IsTCErrorMsg-BinderType : ∀ {b} → IsTCErrorMsg (BinderType b)
  IsTCErrorMsg-BinderType .toTCErrorMsg b = inj₁ (show b)

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
    toEfficientDef d@(≔ x) Γ = record d { extra = just $ genExtra false (globalToContext Γ) $ Erase x }
    toEfficientDef d Γ = d

module StringErr ⦃ _ : Monad M ⦄ ⦃ _ : MonadExcept M String ⦄ where

  beqMonadHelper : ⦃ _ : EqB A ⦄ ⦃ _ : Show A ⦄ → A → A → String → M ⊤
  beqMonadHelper a a' s =
    if a ≣ a'
      then return tt
      else throwError (s <+> show a <+> "isn't equal to" <+> s <+> show a')

  {-# TERMINATING #-}
  pureTermBeq : PureTerm → PureTerm → M ⊤
  pureTermBeq (Var x)       (Var x₁)        = beqMonadHelper x x₁ "Name"
  pureTermBeq (Sort-T x)    (Sort-T x₁)     = beqMonadHelper x x₁ "Sort"
  pureTermBeq (Const-T x)   (Const-T x₁)    = beqMonadHelper x x₁ "Const"
  pureTermBeq (App b t t₁)  (App b' x x₁)   = beqMonadHelper b b' "Binder" >> pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Lam-P b _ t) (Lam-P b' _ t₁) = beqMonadHelper b b' "Binder" >> pureTermBeq t t₁
  pureTermBeq (Pi b _ t t₁) (Pi b' _ x x₁) =
    beqMonadHelper b b' "Binder" >> pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Iota _ t t₁) (Iota _ x x₁)   = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Eq-T t t₁)   (Eq-T x x₁)     = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (M-T t)       (M-T x)         = pureTermBeq x t
  pureTermBeq (Mu t t₁)     (Mu x x₁)       = pureTermBeq t x >> pureTermBeq t₁ x₁
  pureTermBeq (Epsilon t)   (Epsilon x)     = pureTermBeq t x
  pureTermBeq (Ev m t) (Ev m' x) with m ≟ m'
  ... | yes refl = void $ primMetaArgsSequence $ primMetaArgsZipWith pureTermBeq t x
  ... | no  _    = throwError $ show m <+> "and" <+> show m' <+> "aren't equal!"
  {-# CATCHALL #-}
  pureTermBeq t t' =
    throwError $ "The terms" <+> show t <+> "and" <+> show t' <+> "aren't equal!"

  module _ (Γ : Context) where
    compareNames : PureTerm → PureTerm → M ⊤
    compareNames (Var x) (Var x₁) =
      if x ≣ x₁
        then return tt
        else throwError "Names not equal! If you see this message, this is a bug!"
    {-# CATCHALL #-}
    compareNames _ _ = throwError "Terms are not names! If you see this message, this is a bug!"

    {-# NON_TERMINATING #-}
    checkβηPure' : ℕ → PureTerm → PureTerm → M ⊤
    checkβηPure' 0 _ _ = throwError "checkβηPure: out of fuel"
    checkβηPure' (suc n) t t' = appendIfError
      (tryElse (compareNames t t') $
       tryElse (pureTermBeq t t') $
       tryElse (compareHnfs (N.hnfNorm Γ t) t') $
       tryElse (compareHnfs t             (N.hnfNorm Γ t')) $
                compareHnfs (N.hnfNorm Γ t) (N.hnfNorm Γ t'))
      ("\n\nWhile checking equality of" <+> show t <+> "and" <+> show t'
      + "\nHNFs:" <+> show (N.hnfNorm Γ t) <+> "and" <+> show (N.hnfNorm Γ t'))
      where
        hnfError : PureTerm → PureTerm → M ⊤
        hnfError t t' =
          throwError $ "The terms" <+> show t <+> "and" <+> show t' <+> "aren't equal!"

        compareHnfs : PureTerm → PureTerm → M ⊤
        compareHnfs (Var x) (Var x₁)              = beqMonadHelper x x₁ "Name"
        compareHnfs (Sort-T x) (Sort-T x₁)        = beqMonadHelper x x₁ "Sort"
        compareHnfs (Const-T x) (Const-T x₁)      = beqMonadHelper x x₁ "Const"
        compareHnfs (App b t t₁) (App b' x x₁)    = beqMonadHelper b b' "Binder" >> checkβηPure' n t x >> checkβηPure' n t₁ x₁
        compareHnfs (Lam-P b _ t) (Lam-P b' _ t₁) = beqMonadHelper b b' "Binder" >> checkβηPure' n t t₁
        compareHnfs (Pi b _ t t₁) (Pi b' _ x x₁) =
          beqMonadHelper b b' "Binder" >> checkβηPure' n t x >> checkβηPure' n t₁ x₁
        compareHnfs (Iota _ t t₁) (Iota _ x x₁)   = checkβηPure' n t x >> checkβηPure' n t₁ x₁
        compareHnfs (Eq-T t t₁) (Eq-T x x₁)       = checkβηPure' n t x >> checkβηPure' n t₁ x₁
        compareHnfs (M-T t) (M-T x)               = checkβηPure' n x t
        compareHnfs (Mu t t₁) (Mu x x₁)           = checkβηPure' n t x >> checkβηPure' n t₁ x₁
        compareHnfs (Epsilon t) (Epsilon x)       = checkβηPure' n t x
        compareHnfs t@(Ev m x) t'@(Ev m' x') with m ≟ m'
        ... | yes refl = void $ primMetaArgsSequence $ primMetaArgsZipWith (checkβηPure' n) x x'
        ... | no  _    = hnfError t t'
        compareHnfs (Lam-P _ _ t) t₁ = checkβηPure' n t (weakenBy 1 t₁ ⟪$⟫ BoundVar 0)
        compareHnfs t (Lam-P _ _ t₁) = checkβηPure' n (weakenBy 1 t ⟪$⟫ BoundVar 0) t₁
        {-# CATCHALL #-}
        compareHnfs t t' = hnfError t t'

    checkβηPure = checkβηPure' 100

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
    hnfNorm false Γ t

  {-# TERMINATING #-}
  synthType' : AnnTerm → M AnnTerm

  synthType' tm@(Var x) = do
    Γ ← ask
    case (lookupTypeInContext x Γ) of λ
      { (just T) → return T
      ; nothing → throwErrorCtx tm
        (("Lookup failed:" <+> show x + "\nIn context:" <+> show {{Context-Show}} Γ) ∷ᵗ []) }

  synthType' ⋆ = return □
  synthType' □ = throwError1 □ "Cannot synthesize type for the kind □"

  synthType' tm@(Const-T CharT)     = return ⋆
  synthType' tm@(Const-T (CharC c)) = return $ Const-T CharT
  synthType' tm@(Const-T CharEq)    = return $ Const-T CharT ⟪→⟫ Const-T CharT ⟪→⟫ FreeVar "Bool"
  synthType' tm@(Const-T MM)        = return $ ⋆ ⟪→⟫ ⋆
  synthType' tm@(Const-T MuM)       = return $
    Pi Erased  "X" ⋆ $ Pi Erased  "Y" ⋆ $
    M-T (BoundVar 1) ⟪→⟫ (BoundVar 2 ⟪→⟫ M-T (BoundVar 2)) ⟪→⟫ M-T (BoundVar 2)
  synthType' tm@(Const-T EpsilonM)  = return $
    Pi Erased "X" ⋆ $ BoundVar 0 ⟪→⟫ M-T (BoundVar 1)
  synthType' tm@(Const-T CatchM)    = return $
    Pi Erased  "X" ⋆ $
    M-T (BoundVar 0) ⟪→⟫ (FreeVar "init$err" ⟪→⟫ M-T (BoundVar 2)) ⟪→⟫ M-T (BoundVar 2)
  synthType' tm@(Const-T Fix)       = return $
    Pi Erased  "X" ⋆ $
    (BoundVar 0 ⟪→⟫ BoundVar 1) ⟪→⟫ FreeVar "Top"

  synthType' tm@(Pr1 t) = do
    T ← synthType' t
    (Iota _ u u₁) ← hnfNormM T
      where _ → throwError1 tm "Term does not reduce to an iota term"
    return u

  synthType' tm@(Pr2 t) = do
    T ← synthType' t
    (Iota _ u u₁) ← hnfNormM T
      where _ → throwError1 tm "Term does not reduce to an iota term"
    return $ subst u₁ (Pr1 t)

  synthType' tm@(Beta t t₁) = do
    T ← synthType' (Eq-T t t)
    ⋆ ← hnfNormM T
      where _ → throwError1 tm "Equality type does not have the right type. Is this a bug?"
    return $ Eq-T t t

  synthType' tm@(Delta t t₁) = do
    Γ ← ask
    T ← synthType' t₁
    (Eq-T u u₁) ← hnfNormM T
      where _ → throwError1 tm "The second argument of a delta needs to be of an eq type"
    u'  ← normalize false Γ $ Erase u
    u₁' ← normalize false Γ $ Erase u₁
    appendIfError'
      (pureTermBeq u'  (Lam-P Regular "" $ Lam-P Regular "" $ BoundVar 1) >>
       pureTermBeq u₁' (Lam-P Regular "" $ Lam-P Regular "" $ BoundVar 0))
      tm ("This equality cannot be used for the delta term:" ∷ᵗ u ∷ᵗ "=" ∷ᵗ u₁ ∷ᵗ [])
    return t

  synthType' tm@(Sigma t) = do
    T ← synthType' t
    (Eq-T u u₁) ← hnfNormM T
      where _ → throwError1 tm "Sigma needs an inhabitant of an eq type as argument"
    return $ Eq-T u₁ u

  synthType' tm@(App b t t₁) = do
    Γ ← ask
    T ← synthType' t
    T₁ ← synthType' t₁
    (Pi b' _ u u₁) ← hnfNormM T
      where v → throwErrorCtx tm $
             "The left term in an application needs to have a pi type, while it has type" ∷ᵗ v ∷ᵗ []
    true ← return (b ≣ b')
      where false → throwErrorCtx tm ("The types of binders need to match:" ∷ᵗ b ∷ᵗ "≠" ∷ᵗ b' ∷ᵗ [])
    appendIfError' (checkβη Γ T₁ u) tm
      ("Type mismatch in application:" ∷ᵗ tm ∷ᵗ "\nThe type of RHS," ∷ᵗ
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

  synthType' tm@(Pi b n t t₁) = do
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
    true ← return $ if b ≣ Erased then s' ≣ Ast else true
      where _ → throwErrorCtx tm $
             "The type familiy in an erased pi should have sort ⋆, but it has sort □"
             ∷ᵗ "\nContext:" <+> show {{Context-Show}} Γ' ∷ᵗ []
    return $ Sort-T s'

  synthType' tm@(Iota n t t₁) = do
    Γ ← ask
    u ← synthType' t
    ⋆ ← hnfNormM u
      where v → throwErrorCtx tm $
             "The type of the parameter type in iota should be ⋆, but it has type" ∷ᵗ v ∷ᵗ []
    let Γ' = pushType Γ (n , t)
    u₁ ← local (λ _ → Γ') $ synthType' t₁
    ⋆ ← hnfNorm false Γ' u₁
      where v → throwErrorCtx tm $
                  "The type family in iota should have type ⋆, but it has type"
                  ∷ᵗ v ∷ᵗ "\nContext:" <+> show {{Context-Show}} Γ' ∷ᵗ []
    return ⋆

  synthType' tm@(Lam-A b n t t₁) = do
    false ← return (b ≣ Erased ∧ checkFree (Bound 0) (Erase t₁))
      where true → throwErrorCtx tm $
                      "Erased argument" ∷ᵗ (BoundVar 0) ∷ᵗ "cannot appear in a relevant position!\nIn: "
                      ∷ᵗ show (Erase {b = false} t₁) ∷ᵗ []
    synthType' t
    u ← local (flip pushType (n , t)) $ synthType' t₁
    return $ Pi b n t u

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
    ⋆ ← hnfNormM u₂
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
    ⋆ ← hnfNormM T
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
    (Pi Regular _ v v₁) ← hnfNormM T'
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

synthType : ⦃ _ : Monad M ⦄ ⦃ _ : MonadExcept M String ⦄ → Context → AnnTerm → M AnnTerm
synthType Γ t = do
  (inj₂ t) ← map₁ (show ⦃ Show-TCError ⦄) <$>
    synthType' ⦃ ExceptT-Monad ⦃ Monad-ReaderT ⦄ ⦄
               ⦃ ExceptT-MonadReader ⦃ Monad-ReaderT ⦄ ⦃ MonadReader-ReaderT ⦄ ⦄
               ⦃ ExceptT-MonadExcept ⦃ Monad-ReaderT ⦄ ⦄
               t Γ
    where (inj₁ msg) → throwError msg
  return t
