open import Prelude
open import Theory.Terms

module Theory.Context where

open import Prelude.Nat

open import Data.HSTrie
open import Class.Map
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
  Context-Show .show (fst , snd) = (show $ length snd) <+> "local variables:" + show snd

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
validInContext : PureTerm false → Context → Bool
validInContext = helper 0
  where
    -- instead of modifying the context here, we just count how many variables we would have added if we did
    helper : 𝕀 → PureTerm false → Context → Bool
    helper k (Var-T (Bound x))  Γ = x <𝕀 (fromℕ (localContextLength Γ) +𝕀 k)
    helper k (Var-T n@(Free x)) Γ = maybe (λ _ → true) false $ lookupInContext n Γ
    helper k (Sort-T x)         Γ = true
    helper k (Const-T x)        Γ = true
    helper k (App t t₁)         Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Lam-P _ t)        Γ = helper (suc𝕀 k) t Γ
    helper k (Pi _ t t₁)        Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
    helper k (All _ t t₁)       Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
    helper k (Iota _ t t₁)      Γ = helper k t Γ ∧ helper (suc𝕀 k) t₁ Γ
    helper k (Eq-T t t₁)        Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (M-T t)            Γ = helper k t Γ
    helper k (Mu t t₁)          Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Epsilon t)        Γ = helper k t Γ
    helper k (Gamma t t₁)       Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Ev m t)           Γ = primMetaArgsAnd $ mapPrimMetaArgs (λ x → helper k x Γ) t
    helper k (Char-T c)         Γ = true
    helper k (CharEq t t₁)      Γ = helper k t Γ ∧ helper k t₁ Γ

isLocallyClosed : PureTerm false → Context → Bool
isLocallyClosed t (Γ , _) = validInContext t (Γ , [])
