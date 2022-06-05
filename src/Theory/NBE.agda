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
  _⊔_ : 𝕀 → 𝕀 → 𝕀
  _⊔_ = _⊔𝕀_

  Context' : Set
  Context' = GlobalContext × List (String × Maybe (PureTerm true))

  {-# TERMINATING #-}
  fromPureTerm : PureTerm false → PureTerm true
  fromPureTerm (Var-P x)       = Var-P x
  fromPureTerm (Sort-P x)      = Sort-P x
  fromPureTerm (Const-P x)     = Const-P x
  fromPureTerm (App-P t t₁)    = App-P (fromPureTerm t) (fromPureTerm t₁)
  fromPureTerm (Lam-P x t)     = Lam-P x (fromPureTerm t)
  fromPureTerm (Pi-P x t t₁)   = Pi-P x (fromPureTerm t) (fromPureTerm t₁)
  fromPureTerm (All-P x t t₁)  = All-P x (fromPureTerm t) (fromPureTerm t₁)
  fromPureTerm (Iota-P x t t₁) = Iota-P x (fromPureTerm t) (fromPureTerm t₁)
  fromPureTerm (Eq-P t t₁)     = Eq-P (fromPureTerm t) (fromPureTerm t₁)
  fromPureTerm (M-P t)         = M-P (fromPureTerm t)
  fromPureTerm (Mu-P t t₁)     = Mu-P (fromPureTerm t) (fromPureTerm t₁)
  fromPureTerm (Epsilon-P t)   = Epsilon-P (fromPureTerm t)
  fromPureTerm (Gamma-P t t₁)  = Gamma-P (fromPureTerm t) (fromPureTerm t₁)
  fromPureTerm (Ev-P m x)      = Ev-P m (mapPrimMetaArgs fromPureTerm x)
  fromPureTerm (Char-P x)      = Char-P x
  fromPureTerm (CharEq-P t t₁) = CharEq-P (fromPureTerm t) (fromPureTerm t₁)

  -- add abstract variables so that the term has no free DB's
  {-# TERMINATING #-}
  adjustContext : Context' → PureTerm true → Context'
  adjustContext Γ t = flip map₂ Γ (λ Γ' →
    mapWithIndex (λ i → map₂ (_<∣> just (FDB-P $ fromℕ i)))
      (Γ' ++ replicate (necessaryVars t ∸ length Γ') ("_" , nothing)))
    where
      necessaryVars : PureTerm true → ℕ
      necessaryVars = toℕ ∘ helper 0 0
        where
          helper : 𝕀 → ℕ → PureTerm true → 𝕀
          helper i accu (Var-P (Bound x)) = suc𝕀 x -𝕀 i
          helper i accu (Var-P (Free x))  = 0
          helper i accu (FDB-P x)         = error "Error 1 in necessaryVars"
          helper i accu (Sort-P x)        = 0
          helper i accu (Const-P x)       = 0
          helper i accu (App-P t t₁)      = helper i accu t ⊔ helper i accu t₁
          helper i accu (Lam-P x t)       = helper (suc𝕀 i) accu t
          helper i accu (Cont-P n t x)    = error "Error 2 in necessaryVars"
          helper i accu (Pi-P x t t₁)     = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
          helper i accu (All-P x t t₁)    = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
          helper i accu (Iota-P x t t₁)   = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
          helper i accu (Eq-P t t₁)       = helper i accu t ⊔ helper i accu t₁
          helper i accu (M-P t)           = helper i accu t
          helper i accu (Mu-P t t₁)       = helper i accu t ⊔ helper i accu t₁
          helper i accu (Epsilon-P t)     = helper i accu t
          helper i accu (Gamma-P t t₁)    = helper i accu t ⊔ helper i accu t₁
          helper i accu (Ev-P m x)        = primMetaArgsMax $ mapPrimMetaArgs (helper i accu) x
          helper i accu (Char-P x)        = 0
          helper i accu (CharEq-P t t₁)   = helper i accu t ⊔ helper i accu t₁

  pushTerm : Context' → String → PureTerm true → Context'
  pushTerm (Γ , Γ') n t = (Γ , (n , just t) ∷ Γ')

  pushAbstract : Context' → String → Context'
  pushAbstract (Γ , Γ') n = (Γ , (n , nothing) ∷ Γ')

  module Lookup (conv : Def → Maybe (PureTerm true)) where

    lookupInContext' : Context' → Name → Maybe (PureTerm true)
    lookupInContext' (Γ , Γ') (Bound x)  = proj₂ =<< lookupMaybe (toℕ x) Γ'
    lookupInContext' (Γ , Γ') n@(Free x) = conv =<< lookupInContext n (Γ , [])

    lookup' : Context' → Name → PureTerm true
    lookup' Γ n = maybe id (Var n) $ lookupInContext' Γ n

  module Conv (nf' : Context' → PureTerm true → PureTerm true)
              (convDef : Def → Maybe (PureTerm true)) where
    {-# TERMINATING #-}
    toPureTerm : ℕ → Context' → PureTerm true → PureTerm false
    toPureTerm k Γ (Var-P x)       = Var-P x
    toPureTerm k Γ (FDB-P x)       = Var-P (Bound (x +𝕀 fromℕ k))
    toPureTerm k Γ (Sort-P x)      = Sort-P x
    toPureTerm k Γ (Const-P x)     = Const-P x
    toPureTerm k Γ (App-P t t₁)    = App-P (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (Lam-P x t)     = Lam-P x (toPureTerm (suc k) Γ t)
    toPureTerm k Γ (Pi-P x t t₁)   = Pi-P x (toPureTerm k Γ t) (toPureTerm (suc k) Γ t₁)
    toPureTerm k Γ (All-P x t t₁)  = All-P x (toPureTerm k Γ t) (toPureTerm (suc k) Γ t₁)
    toPureTerm k Γ (Iota-P x t t₁) = Iota-P x (toPureTerm k Γ t) (toPureTerm (suc k) Γ t₁)
    toPureTerm k Γ (Eq-P t t₁)     = Eq-P (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (M-P t)         = M-P (toPureTerm k Γ t)
    toPureTerm k Γ (Mu-P t t₁)     = Mu-P (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (Epsilon-P t)   = Epsilon-P (toPureTerm k Γ t)
    toPureTerm k Γ (Gamma-P t t₁)  = Gamma-P (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (Ev-P m x)      = Ev-P m (mapPrimMetaArgs (toPureTerm k Γ) x)
    toPureTerm k Γ (Char-P x)      = Char-P x
    toPureTerm k Γ (CharEq-P t t₁) = CharEq-P (toPureTerm k Γ t) (toPureTerm k Γ t₁)
    toPureTerm k Γ (Cont-P n Γ' t) = Lam-P n (toPureTerm (suc k) Γ (nf' (pushAbstract (proj₁ Γ , Γ') n) t))

    convContext : Context → Context'
    convContext (Γ , Γ') = (Γ , map (map₂ convDef) Γ')

    nf : Context → PureTerm false → PureTerm false
    nf Γ t = let t' = fromPureTerm t
      in toPureTerm (length (proj₂ Γ)) (convContext Γ) $ nf' (adjustContext (convContext Γ) t') t'

module _ where
  private
    convDef : Def → Maybe (PureTerm true)
    convDef record { extra = extra } = extra

    open Lookup convDef

    {-# NON_TERMINATING #-}
    dbnf : Context' → PureTerm true → PureTerm true
    dbnf Γ (Var-P x)           = lookup' Γ x
    dbnf Γ (FDB-P x)           = FDB-P x
    dbnf Γ (Sort-P x)          = Sort-P x
    dbnf Γ (Const-P x)         = Const-P x
    dbnf Γ (App-P t t₁) with dbnf Γ t | dbnf Γ t₁
    ... | (Cont-P n Γ' x) | x₁ = dbnf (pushTerm (proj₁ Γ , Γ') n x₁) x
    ... | x               | x₁ = App-P x x₁
    dbnf Γ (Lam-P x t)         = Cont-P x (proj₂ Γ) t
    dbnf Γ (Cont-P n Γ' t)     = error "Error in dbnf"
    dbnf Γ (Pi-P x t t₁)       = Pi-P x (dbnf Γ t) (dbnf (pushAbstract Γ x) t₁)
    dbnf Γ (All-P x t t₁)      = All-P x (dbnf Γ t) (dbnf (pushAbstract Γ x) t₁)
    dbnf Γ (Iota-P x t t₁)     = Iota-P x (dbnf Γ t) (dbnf (pushAbstract Γ x) t₁)
    dbnf Γ (Eq-P t t₁)         = Eq-P (dbnf Γ t) (dbnf Γ t₁)
    dbnf Γ (M-P t)             = M-P (dbnf Γ t)
    dbnf Γ (Mu-P t t₁)         = Mu-P (dbnf Γ t) (dbnf Γ t₁)
    dbnf Γ (Epsilon-P t)       = Epsilon-P (dbnf Γ t)
    dbnf Γ (Gamma-P t t₁)      = Gamma-P (dbnf Γ t) (dbnf Γ t₁)
    dbnf Γ (Ev-P m x)          = Ev-P m (mapPrimMetaArgs (dbnf Γ) x)
    dbnf Γ (Char-P x)          = Char-P x
    dbnf Γ (CharEq-P t t₁) with dbnf Γ t | dbnf Γ t₁
    ... | Char-P c | Char-P c₁ = dbnf Γ $ Var $ Free $ show (c ≣ c₁)
    ... | t        | t₁        = CharEq-P t t₁

  module C = Conv dbnf convDef
  open C using (nf) public

  genExtra : Context → PureTerm false → PureTerm true
  genExtra Γ t = dbnf (C.convContext Γ) $ fromPureTerm t

module _ where
  private
    convDef : Def → Maybe (PureTerm true)
    convDef record { def = def } = fromPureTerm ∘ Erase <$> def

    open Lookup convDef

    -- Whether to reduce
    {-# NON_TERMINATING #-}
    hnf' : Bool → Context' → PureTerm true → PureTerm true
    hnf' true Γ (Var-P x) with lookupInContext' Γ x
    ... | just y                  = hnf' true Γ y
    ... | nothing                 = Var-P x
    hnf' false Γ (Var-P (Bound x)) = lookup' Γ (Bound x)
    hnf' false Γ (Var-P (Free x))  = Var-P (Free x)
    hnf' b Γ (FDB-P x)             = FDB-P x
    hnf' b Γ (Sort-P x)            = Sort-P x
    hnf' b Γ (Const-P x)           = Const-P x
    hnf' true Γ (App-P t t₁) with hnf' true Γ t | hnf' false Γ t₁
    ... | Cont-P n Γ' x | x₁      = hnf' true (pushTerm (proj₁ Γ , Γ') n x₁) x
    ... | x             | x₁      = App-P x x₁
    hnf' false Γ (App-P t t₁)      = App-P (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' true  Γ (Lam-P x t)       = Cont-P x (proj₂ Γ) t
    hnf' false Γ (Lam-P x t)       = Lam-P x (hnf' false (pushAbstract Γ x) t)
    hnf' b Γ (Cont-P _ _ _)        = error "Error in hnf'"
    hnf' b Γ (Pi-P x t t₁)         = Pi-P x (hnf' false Γ t) (hnf' false (pushAbstract Γ x) t₁)
    hnf' b Γ (All-P x t t₁)        = All-P x (hnf' false Γ t) (hnf' false (pushAbstract Γ x) t₁)
    hnf' b Γ (Iota-P x t t₁)       = Iota-P x (hnf' false Γ t) (hnf' false (pushAbstract Γ x) t₁)
    hnf' b Γ (Eq-P t t₁)           = Eq-P (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' b Γ (M-P t)               = M-P (hnf' false Γ t)
    hnf' b Γ (Mu-P t t₁)           = Mu-P (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' b Γ (Epsilon-P t)         = Epsilon-P (hnf' false Γ t)
    hnf' b Γ (Gamma-P t t₁)        = Gamma-P (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' b Γ (Ev-P m x)            = Ev-P m (mapPrimMetaArgs (hnf' false Γ) x)
    hnf' b Γ (Char-P x)            = Char-P x
    hnf' b Γ (CharEq-P t t₁) with hnf' b Γ t | hnf' b Γ t₁
    ... | Char-P c | Char-P c₁    = hnf' b Γ $ Var $ Free $ show (c ≣ c₁)
    ... | t        | t₁           = CharEq-P t t₁

    hnf = hnf' true

  open Conv hnf convDef using () renaming (nf to hnf) public
