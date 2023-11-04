module Theory.Context where

open import Prelude
open import Prelude.Nat
open import Theory.Terms

open import Class.Map
open import Data.HSTrie
open import Data.Word using (toℕ; fromℕ)

record Def : Set where
  field def   : Maybe AnnTerm
        type  : AnnTerm
        extra : Maybe (PureTerm true)

instance
  Def-Show : Show Def
  Def-Show .show record { def = (just d) ; type = t } = " :=" <+> show d <+> ":" <+> show t
  Def-Show .show record { def = nothing  ; type = t } = " :" <+> show t

pattern ≔ d = record { def = just d }
pattern ∶ t = record { type = t }

GlobalContext : Set
GlobalContext = HSTrie Def

emptyGlobalContext : GlobalContext
emptyGlobalContext = emptyMap

Context : Set
Context = GlobalContext × List (String × Def)

instance
  Context-Show : Show Context
  Context-Show .show (fst , snd) = (show $ length snd) <+> "local variables:" <+> show snd

globalToContext : GlobalContext → Context
globalToContext Γ = Γ , []

contextToGlobal : Context → GlobalContext
contextToGlobal (fst , snd) = fst

pushDef : Context → String × Def → Context
pushDef (fst , snd) v = fst , v ∷ snd

pushType : Context → String × AnnTerm → Context
pushType Γ (n , t) = pushDef Γ (n , record { def = nothing ; type = t ; extra = nothing })

private
  localContextLength : Context → ℕ
  localContextLength (fst , snd) = length snd

lookupInContext : Name → Context → Maybe Def
lookupInContext (Bound x) (fst , snd) =
  proj₂ <$> lookupMaybe (toℕ x) snd
lookupInContext (Free x) (fst , snd) = lookup x fst

lookupTypeInContext : Name → Context → Maybe AnnTerm
lookupTypeInContext n@(Bound x) Γ with lookupInContext n Γ
... | just (∶ T) = just $ weakenBy (suc𝕀 x) T
... | _ = nothing
lookupTypeInContext n Γ = Def.type <$> lookupInContext n Γ

{-# TERMINATING #-}
validInContext : ∀ {a} → Term a false → Context → Bool
validInContext {a} = helper 0
  where
    -- instead of modifying the context here, we just count how many variables we would have added if we did
    helper : 𝕀 → Term a false → Context → Bool
    helper k (Var (Bound x))  Γ = x <𝕀 (fromℕ (localContextLength Γ) +𝕀 k)
    helper k (Var n@(Free x)) Γ = maybe (λ _ → true) false $ lookupInContext n Γ
    helper k (Sort-T x)       Γ = true
    helper k (Const-T x)      Γ = true
    helper k (App _ t t₁)     Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Lam-P _ _ t)    Γ = helper (suc𝕀 k) t Γ
    helper k (Lam-A _ _ t t₁) Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
    helper k (Pi _ _ t t₁)    Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
    helper k (Iota _ t t₁)    Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
    helper k (Eq-T t t₁)      Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (M-T t)          Γ = helper k t Γ
    helper k (Mu t t₁)        Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Epsilon t)      Γ = helper k t Γ
    helper k (Ev m t)         Γ = primMetaArgsAnd $ mapPrimMetaArgs (λ x → helper k x Γ) t
    helper k (Pr1 t)          Γ = helper k t Γ
    helper k (Pr2 t)          Γ = helper k t Γ
    helper k (Beta t t₁)      Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Delta t t₁)     Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Sigma t)        Γ = helper k t Γ
    helper k (Rho t t₁ t₂)    Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ ∧ helper k t₂ Γ
    helper k (Pair t t₁ t₂)   Γ = helper k t Γ ∧ helper k t₁ Γ ∧ helper (suc𝕀 k) t₂ Γ
    helper k (Phi t t₁ t₂)    Γ = helper k t Γ ∧ helper k t₁ Γ ∧ helper k t₂ Γ

isLocallyClosed : ∀ {a} → Term a false → Context → Bool
isLocallyClosed t (Γ , _) = validInContext t (Γ , [])
