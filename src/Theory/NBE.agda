-- Based on NBE.Felgenhauer in lambda-n-ways

module Theory.NBE where

open import Prelude hiding (_⊔_)
open import Prelude.Nat
open import Unsafe using (error)

open import Data.Word using (toℕ; fromℕ)
open import Theory.Context
open import Theory.Names
open import Theory.PrimMeta
open import Theory.Terms

private
  variable b : Bool

  infixl 5 _⊔_
  _⊔_ : 𝕀 → 𝕀 → 𝕀
  _⊔_ = _⊔𝕀_

  Context' : Bool → Set
  Context' b = GlobalContext × List (String × Maybe (Term b true))

  {-# TERMINATING #-}
  toNBETerm : Term b false → Term b true
  toNBETerm (Var-T x)      = Var-T x
  toNBETerm (Sort-T x)     = Sort-T x
  toNBETerm (Const-T x)    = Const-T x
  toNBETerm (App t t₁)     = App (toNBETerm t) (toNBETerm t₁)
  toNBETerm (AppE t t₁)    = AppE (toNBETerm t) (toNBETerm t₁)
  toNBETerm (Lam-P x t)    = Lam-P x (toNBETerm t)
  toNBETerm (Lam-A x t t₁) = Lam-A x (toNBETerm t) (toNBETerm t₁)
  toNBETerm (LamE x t t₁)  = LamE x (toNBETerm t) (toNBETerm t₁)
  toNBETerm (Pi x t t₁)    = Pi x (toNBETerm t) (toNBETerm t₁)
  toNBETerm (All x t t₁)   = All x (toNBETerm t) (toNBETerm t₁)
  toNBETerm (Iota x t t₁)  = Iota x (toNBETerm t) (toNBETerm t₁)
  toNBETerm (Eq-T t t₁)    = Eq-T (toNBETerm t) (toNBETerm t₁)
  toNBETerm (M-T t)        = M-T (toNBETerm t)
  toNBETerm (Mu t t₁)      = Mu (toNBETerm t) (toNBETerm t₁)
  toNBETerm (Epsilon t)    = Epsilon (toNBETerm t)
  toNBETerm (Gamma t t₁)   = Gamma (toNBETerm t) (toNBETerm t₁)
  toNBETerm (Ev m x)       = Ev m (mapPrimMetaArgs toNBETerm x)
  toNBETerm (Char-T x)     = Char-T x
  toNBETerm (CharEq t t₁)  = CharEq (toNBETerm t) (toNBETerm t₁)
  toNBETerm (Pr1 t)        = Pr1 (toNBETerm t)
  toNBETerm (Pr2 t)        = Pr2 (toNBETerm t)
  toNBETerm (Beta t t')    = Beta (toNBETerm t) (toNBETerm t')
  toNBETerm (Delta t t')   = Delta (toNBETerm t) (toNBETerm t')
  toNBETerm (Sigma t)      = Sigma (toNBETerm t)
  toNBETerm (Rho t t₁ t₂)  = Rho (toNBETerm t) (toNBETerm t₁) (toNBETerm t₂)
  toNBETerm (Pair t t₁ t₂) = Pair (toNBETerm t) (toNBETerm t₁) (toNBETerm t₂)
  toNBETerm (Phi t t₁ t₂)  = Phi (toNBETerm t) (toNBETerm t₁) (toNBETerm t₂)

  -- add abstract variables so that the term has no free DB's
  {-# TERMINATING #-}
  adjustContext : Context' b → Term b true → Context' b
  adjustContext Γ t = flip map₂ Γ (λ Γ' →
    mapWithIndex (λ i → map₂ (_<∣> just (FDB $ fromℕ i)))
      (Γ' ++ replicate (necessaryVars t ∸ length Γ') ("_" , nothing)))
    where
      necessaryVars : Term b true → ℕ
      necessaryVars = toℕ ∘ helper 0 0
        where
          helper : 𝕀 → ℕ → Term b true → 𝕀
          helper i accu (Var-T (Bound x)) = suc𝕀 x -𝕀 i
          helper i accu (Var-T (Free x))  = 0
          helper i accu (FDB x)           = error "Error 1 in necessaryVars"
          helper i accu (Sort-T x)        = 0
          helper i accu (Const-T x)       = 0
          helper i accu (App t t₁)        = helper i accu t ⊔ helper i accu t₁
          helper i accu (AppE t t₁)       = helper i accu t ⊔ helper i accu t₁
          helper i accu (Lam-P x t)       = helper (suc𝕀 i) accu t
          helper i accu (Lam-A x t t₁)    = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
          helper i accu (LamE x t t₁)     = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
          helper i accu (Cont n t x)      = error "Error 2 in necessaryVars"
          helper i accu (Pi x t t₁)       = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
          helper i accu (All x t t₁)      = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
          helper i accu (Iota x t t₁)     = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
          helper i accu (Eq-T t t₁)       = helper i accu t ⊔ helper i accu t₁
          helper i accu (M-T t)           = helper i accu t
          helper i accu (Mu t t₁)         = helper i accu t ⊔ helper i accu t₁
          helper i accu (Epsilon t)       = helper i accu t
          helper i accu (Gamma t t₁)      = helper i accu t ⊔ helper i accu t₁
          helper i accu (Ev m x)          = primMetaArgsMax $ mapPrimMetaArgs (helper i accu) x
          helper i accu (Char-T x)        = 0
          helper i accu (CharEq t t₁)     = helper i accu t ⊔ helper i accu t₁
          helper i accu (Pr1 t)           = helper i accu t
          helper i accu (Pr2 t)           = helper i accu t
          helper i accu (Beta t t')       = helper i accu t ⊔ helper i accu t'
          helper i accu (Delta t t')      = helper i accu t ⊔ helper i accu t'
          helper i accu (Sigma t)         = helper i accu t
          helper i accu (Rho t t₁ t₂)     = helper i accu t ⊔ helper (suc𝕀 i) accu t₁ ⊔ helper i accu t₂
          helper i accu (Pair t t₁ t₂)    = helper i accu t ⊔ helper i accu t₁ ⊔ helper (suc𝕀 i) accu t₂
          helper i accu (Phi t t₁ t₂)     = helper i accu t ⊔ helper i accu t₁ ⊔ helper i accu t₂

  pushTerm : Context' b → String → Term b true → Context' b
  pushTerm (Γ , Γ') n t = (Γ , (n , just t) ∷ Γ')

  pushAbstract : Context' b → String → Context' b
  pushAbstract (Γ , Γ') n = (Γ , (n , nothing) ∷ Γ')

  module Lookup (conv : Def → Maybe (Term b true)) where

    lookupInContext' : Context' b → Name → Maybe (Term b true)
    lookupInContext' (Γ , Γ') (Bound x)  = proj₂ =<< lookupMaybe (toℕ x) Γ'
    lookupInContext' (Γ , Γ') n@(Free x) = conv =<< lookupInContext n (Γ , [])

    lookup' : Context' b → Name → Term b true
    lookup' Γ n = maybe id (Var n) $ lookupInContext' Γ n

  module Conv (nf' : Context' false → Term false true → Term false true)
              (convDef : Def → Maybe (Term false true)) where
    {-# TERMINATING #-}
    toPureTerm : ℕ → Context' false → Term false true → Term false false
    toPureTerm k Γ (Var-T x)     = Var-T x
    toPureTerm k Γ (FDB x)       = Var (Bound (x +𝕀 fromℕ k))
    toPureTerm k Γ (Sort-T x)    = Sort-T x
    toPureTerm k Γ (Const-T x)   = Const-T x
    toPureTerm k Γ (App t t₁)    = App (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (Lam-P x t)   = Lam-P x (toPureTerm (suc k) Γ t)
    toPureTerm k Γ (Pi x t t₁)   = Pi x (toPureTerm k Γ t) (toPureTerm (suc k) Γ t₁)
    toPureTerm k Γ (All x t t₁)  = All x (toPureTerm k Γ t) (toPureTerm (suc k) Γ t₁)
    toPureTerm k Γ (Iota x t t₁) = Iota x (toPureTerm k Γ t) (toPureTerm (suc k) Γ t₁)
    toPureTerm k Γ (Eq-T t t₁)   = Eq-T (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (M-T t)       = M-T (toPureTerm k Γ t)
    toPureTerm k Γ (Mu t t₁)     = Mu (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (Epsilon t)   = Epsilon (toPureTerm k Γ t)
    toPureTerm k Γ (Gamma t t₁)  = Gamma (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (Ev m x)      = Ev m (mapPrimMetaArgs (toPureTerm k Γ) x)
    toPureTerm k Γ (Char-T x)    = Char-T x
    toPureTerm k Γ (CharEq t t₁) = CharEq (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (Cont n Γ' t) = Lam-P n (toPureTerm (suc k) Γ (nf' (pushAbstract (proj₁ Γ , Γ') n) t))

    convContext : Context → Context' false
    convContext (Γ , Γ') = (Γ , map (map₂ convDef) Γ')

    nf : Context → PureTerm false → PureTerm false
    nf Γ t = let t' = toNBETerm t
      in toPureTerm (length (proj₂ Γ)) (convContext Γ) $ nf' (adjustContext (convContext Γ) t') t'

module _ where
  private
    convDef : Def → Maybe (Term false true)
    convDef record { extra = extra } = extra

    open Lookup convDef

    {-# NON_TERMINATING #-}
    dbnf : Context' false → PureTerm true → PureTerm true
    dbnf Γ (Var-T x)           = lookup' Γ x
    dbnf Γ (FDB x)             = FDB x
    dbnf Γ (Sort-T x)          = Sort-T x
    dbnf Γ (Const-T x)         = Const-T x
    dbnf Γ (App t t₁) with dbnf Γ t | dbnf Γ t₁
    ... | (Cont n Γ' x) | x₁   = dbnf (pushTerm (proj₁ Γ , Γ') n x₁) x
    ... | x             | x₁   = App x x₁
    dbnf Γ (Lam-P x t)         = Cont x (proj₂ Γ) t
    dbnf Γ (Cont n Γ' t)       = error "Error in dbnf"
    dbnf Γ (Pi x t t₁)         = Pi x (dbnf Γ t) (dbnf (pushAbstract Γ x) t₁)
    dbnf Γ (All x t t₁)        = All x (dbnf Γ t) (dbnf (pushAbstract Γ x) t₁)
    dbnf Γ (Iota x t t₁)       = Iota x (dbnf Γ t) (dbnf (pushAbstract Γ x) t₁)
    dbnf Γ (Eq-T t t₁)         = Eq-T (dbnf Γ t) (dbnf Γ t₁)
    dbnf Γ (M-T t)             = M-T (dbnf Γ t)
    dbnf Γ (Mu t t₁)           = Mu (dbnf Γ t) (dbnf Γ t₁)
    dbnf Γ (Epsilon t)         = Epsilon (dbnf Γ t)
    dbnf Γ (Gamma t t₁)        = Gamma (dbnf Γ t) (dbnf Γ t₁)
    dbnf Γ (Ev m x)            = Ev m (mapPrimMetaArgs (dbnf Γ) x)
    dbnf Γ (Char-T x)          = Char-T x
    dbnf Γ (CharEq t t₁) with dbnf Γ t | dbnf Γ t₁
    ... | Char-T c | Char-T c₁ = dbnf Γ $ Var $ Free $ show (c ≣ c₁)
    ... | t        | t₁        = CharEq t t₁

  module C = Conv dbnf convDef
  open C using (nf) public

  genExtra : Context → PureTerm false → PureTerm true
  genExtra Γ t = dbnf (C.convContext Γ) $ toNBETerm t

module _ where
  private
    convDef : Def → Maybe (Term false true)
    convDef record { def = def } = toNBETerm ∘ Erase <$> def

    open Lookup convDef

    -- Whether to reduce
    {-# NON_TERMINATING #-}
    hnf' : Bool → Context' false → Term false true → Term false true
    hnf' true Γ (Var-T x) with lookupInContext' Γ x
    ... | just y                   = hnf' true Γ y
    ... | nothing                  = Var-T x
    hnf' false Γ (Var-T (Bound x)) = lookup' Γ (Bound x)
    hnf' false Γ (Var-T (Free x))  = Var-T (Free x)
    hnf' b Γ (FDB x)               = FDB x
    hnf' b Γ (Sort-T x)            = Sort-T x
    hnf' b Γ (Const-T x)           = Const-T x
    hnf' true Γ (App t t₁) with hnf' true Γ t | hnf' false Γ t₁
    ... | Cont n Γ' x | x₁         = hnf' true (pushTerm (proj₁ Γ , Γ') n x₁) x
    ... | x             | x₁       = App x x₁
    hnf' false Γ (App t t₁)        = App (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' true  Γ (Lam-P x t)       = Cont x (proj₂ Γ) t
    hnf' false Γ (Lam-P x t)       = Lam-P x (hnf' false (pushAbstract Γ x) t)
    hnf' b Γ (Cont _ _ _)          = error "Error in hnf'"
    hnf' b Γ (Pi x t t₁)           = Pi x (hnf' false Γ t) (hnf' false (pushAbstract Γ x) t₁)
    hnf' b Γ (All x t t₁)          = All x (hnf' false Γ t) (hnf' false (pushAbstract Γ x) t₁)
    hnf' b Γ (Iota x t t₁)         = Iota x (hnf' false Γ t) (hnf' false (pushAbstract Γ x) t₁)
    hnf' b Γ (Eq-T t t₁)           = Eq-T (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' b Γ (M-T t)               = M-T (hnf' false Γ t)
    hnf' b Γ (Mu t t₁)             = Mu (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' b Γ (Epsilon t)           = Epsilon (hnf' false Γ t)
    hnf' b Γ (Gamma t t₁)          = Gamma (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' b Γ (Ev m x)              = Ev m (mapPrimMetaArgs (hnf' false Γ) x)
    hnf' b Γ (Char-T x)            = Char-T x
    hnf' b Γ (CharEq t t₁) with hnf' b Γ t | hnf' b Γ t₁
    ... | Char-T c | Char-T c₁     = hnf' b Γ $ Var $ Free $ show (c ≣ c₁)
    ... | t        | t₁            = CharEq t t₁

    hnf = hnf' true

  open Conv hnf convDef using () renaming (nf to hnf) public
