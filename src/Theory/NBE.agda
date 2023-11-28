{-# OPTIONS --type-in-type #-}
-- Based on NBE.Felgenhauer in lambda-n-ways

module Theory.NBE where

open import Prelude hiding (_⊔_)
open import Prelude.Nat
open import Unsafe using (error)

open import Data.Word using (toℕ; fromℕ)
open import Theory.Context
open import Theory.Terms

private
  variable b : Bool

  infixl 5 _⊔_
  _⊔_ : 𝕀 → 𝕀 → 𝕀
  _⊔_ = _⊔𝕀_

{-# TERMINATING #-}
toNBETerm : Term b false → Term b true
toNBETerm (Var x)          = Var x
toNBETerm (Sort-T x)       = Sort-T x
toNBETerm (Const-T x)      = Const-N x (constArity x)
toNBETerm (App b t t₁)     = App b (toNBETerm t) (toNBETerm t₁)
toNBETerm (Lam-P b x t)    = Lam-P b x (toNBETerm t)
toNBETerm (Lam-A b x t t₁) = Lam-A b x (toNBETerm t) (toNBETerm t₁)
toNBETerm (Pi b x t t₁)    = Pi b x (toNBETerm t) (toNBETerm t₁)
toNBETerm (Iota x t t₁)    = Iota x (toNBETerm t) (toNBETerm t₁)
toNBETerm (Eq-T t t₁)      = Eq-T (toNBETerm t) (toNBETerm t₁)
toNBETerm (M-T t)          = M-T (toNBETerm t)
toNBETerm (Mu t t₁)        = Mu (toNBETerm t) (toNBETerm t₁)
toNBETerm (Epsilon t)      = Epsilon (toNBETerm t)
toNBETerm (Ev m x)         = Ev m (mapPrimMetaArgs toNBETerm x)
toNBETerm (Pr1 t)          = Pr1 (toNBETerm t)
toNBETerm (Pr2 t)          = Pr2 (toNBETerm t)
toNBETerm (Beta t t')      = Beta (toNBETerm t) (toNBETerm t')
toNBETerm (Delta t t')     = Delta (toNBETerm t) (toNBETerm t')
toNBETerm (Sigma t)        = Sigma (toNBETerm t)
toNBETerm (Rho t t₁ t₂)    = Rho (toNBETerm t) (toNBETerm t₁) (toNBETerm t₂)
toNBETerm (Pair t t₁ t₂)   = Pair (toNBETerm t) (toNBETerm t₁) (toNBETerm t₂)
toNBETerm (Phi t t₁ t₂)    = Phi (toNBETerm t) (toNBETerm t₁) (toNBETerm t₂)

Context' : Bool → Set
Context' b = GlobalContext × List (String × Maybe (Term b true))

private
  log' : Bool -> Context' false → Term false true → Term false true → Term false true
  log' doLog Γ t t' = if doLog
    then unsafePerformIO (putStr (show (proj₂ Γ) <+> ":" <+> show t <+> "~>" <+> show t' + "\n") >> return t')
    else t'

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
        helper i accu (Var (Bound x))  = suc𝕀 x -𝕀 i
        helper i accu (Var (Free x))   = 0
        helper i accu (FDB x)          = error "Error 1 in necessaryVars"
        helper i accu (Sort-T x)       = 0
        helper i accu (Const-N _ _)    = 0
        helper i accu (App _ t t₁)     = helper i accu t ⊔ helper i accu t₁
        helper i accu (Lam-P _ x t)    = helper (suc𝕀 i) accu t
        helper i accu (Lam-A _ x t t₁) = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
        helper i accu (Cont n t x)     = error "Error 2 in necessaryVars"
        helper i accu (Pi b x t t₁)    = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
        helper i accu (Iota x t t₁)    = helper i accu t ⊔ helper (suc𝕀 i) accu t₁
        helper i accu (Eq-T t t₁)      = helper i accu t ⊔ helper i accu t₁
        helper i accu (M-T t)          = helper i accu t
        helper i accu (Mu t t₁)        = helper i accu t ⊔ helper i accu t₁
        helper i accu (Epsilon t)      = helper i accu t
        helper i accu (Ev m x)         = primMetaArgsMax $ mapPrimMetaArgs (helper i accu) x
        helper i accu (Pr1 t)          = helper i accu t
        helper i accu (Pr2 t)          = helper i accu t
        helper i accu (Beta t t')      = helper i accu t ⊔ helper i accu t'
        helper i accu (Delta t t')     = helper i accu t ⊔ helper i accu t'
        helper i accu (Sigma t)        = helper i accu t
        helper i accu (Rho t t₁ t₂)    = helper i accu t ⊔ helper (suc𝕀 i) accu t₁ ⊔ helper i accu t₂
        helper i accu (Pair t t₁ t₂)   = helper i accu t ⊔ helper i accu t₁ ⊔ helper (suc𝕀 i) accu t₂
        helper i accu (Phi t t₁ t₂)    = helper i accu t ⊔ helper i accu t₁ ⊔ helper i accu t₂

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
  toPureTerm k Γ (Var x)       = Var x
  toPureTerm k Γ (FDB x)       = Var (Bound (x +𝕀 fromℕ k))
  toPureTerm k Γ (Sort-T x)    = Sort-T x
  toPureTerm k Γ (Const-N x 0) = Const-T x
  toPureTerm k Γ (Const-N x _) = error "toPureTerm Const-N"
  toPureTerm k Γ (App b t t₁)  = App b (toPureTerm k Γ t) (toPureTerm k Γ t₁)
  toPureTerm k Γ (Lam-P b x t) = Lam-P b x (toPureTerm (suc k) Γ t)
  toPureTerm k Γ (Pi b x t t₁) = Pi b x (toPureTerm k Γ t) (toPureTerm (suc k) Γ t₁)
  toPureTerm k Γ (Iota x t t₁) = Iota x (toPureTerm k Γ t) (toPureTerm (suc k) Γ t₁)
  toPureTerm k Γ (Eq-T t t₁)   = Eq-T (toPureTerm k Γ t) (toPureTerm k Γ t₁)
  toPureTerm k Γ (M-T t)       = M-T (toPureTerm k Γ t)
  toPureTerm k Γ (Mu t t₁)     = Mu (toPureTerm k Γ t) (toPureTerm k Γ t₁)
  toPureTerm k Γ (Epsilon t)   = Epsilon (toPureTerm k Γ t)
  toPureTerm k Γ (Ev m x)      = Ev m (mapPrimMetaArgs (toPureTerm k Γ) x)
  toPureTerm k Γ (Cont n Γ' t) = Lam-P Regular n (toPureTerm (suc k) Γ (nf' (pushAbstract (proj₁ Γ , Γ') n) t))

  convContext : Context → Context' false
  convContext (Γ , Γ') = (Γ , map (map₂ convDef) Γ')

  nf : Context → PureTerm false → PureTerm false
  nf Γ t = let t' = toNBETerm t; Γ' = convContext Γ
    in toPureTerm (length (proj₂ Γ)) Γ' $ nf' (adjustContext Γ' t') t'

module _ (doLog : Bool) where
  private
    convDef : Def → Maybe (Term false true)
    convDef record { extra = extra } = extra

    open Lookup convDef
    log = log' doLog

  {-# NON_TERMINATING #-}
  dbnf : Context' false → PureTerm true → PureTerm true
  dbnf Γ v@(Var x)             = log Γ v $ lookup' Γ x
  dbnf Γ v@(FDB x)             = FDB x
  dbnf Γ v@(Sort-T x)          = Sort-T x
  dbnf Γ v@(Const-N x 0)       = log Γ v $ evalConst' (dbnf Γ) x
  dbnf Γ v@(Const-N x (suc k)) = log Γ v $ Cont "" (proj₂ Γ) (Const-N x k)
  dbnf Γ v@(App b t t₁) with dbnf Γ t | dbnf Γ t₁
  ... | (Cont n Γ' x) | x₁   = log (pushTerm (proj₁ Γ , Γ') n x₁) v $ dbnf (pushTerm (proj₁ Γ , Γ') n x₁) x
  ... | x             | x₁   = App b x x₁
  dbnf Γ v@(Lam-P b x t)       = log Γ v $ Cont x (proj₂ Γ) t
  dbnf Γ v@(Cont n Γ' t)       = error ("Error in dbnf:" <+> show v)
  dbnf Γ v@(Pi b x t t₁)       = Pi b x (dbnf Γ t) (dbnf (pushAbstract Γ x) t₁)
  dbnf Γ v@(Iota x t t₁)       = Iota x (dbnf Γ t) (dbnf (pushAbstract Γ x) t₁)
  dbnf Γ v@(Eq-T t t₁)         = Eq-T (dbnf Γ t) (dbnf Γ t₁)
  dbnf Γ v@(M-T t)             = M-T (dbnf Γ t)
  dbnf Γ v@(Mu t t₁)           = Mu (dbnf Γ t) (dbnf Γ t₁)
  dbnf Γ v@(Epsilon t)         = Epsilon (dbnf Γ t)
  dbnf Γ v@(Ev m x)            = Ev m (mapPrimMetaArgs (dbnf Γ) x)

  module C = Conv dbnf convDef
  open C using (nf; toPureTerm) public

  genExtra : Context → PureTerm false → PureTerm true
  genExtra Γ t = dbnf (C.convContext Γ) $ toNBETerm t

module _ (doLog : Bool) where
  private
    convDef : Def → Maybe (Term false true)
    convDef record { def = def } = toNBETerm ∘ Erase <$> def

    log = log' doLog

    open Lookup convDef

    -- Whether to reduce
    {-# NON_TERMINATING #-}
    hnf' : Bool → Context' false → Term false true → Term false true
    hnf' true Γ v@(Var x) with lookupInContext' Γ x
    ... | just y                       = log Γ v $ hnf' true Γ y
    ... | nothing                      = Var x
    hnf' false Γ v@(Var (Bound x))     = log Γ v $ lookup' Γ (Bound x)
    hnf' false Γ v@(Var (Free x))      = v
    hnf' b Γ v@(FDB x)                 = v
    hnf' b Γ v@(Sort-T x)              = v
    hnf' true  Γ v@(Const-N x 0)       = log Γ v $ evalConst' (hnf' true Γ) x
    hnf' true  Γ v@(Const-N x (suc k)) = log Γ v $ Cont "" (proj₂ Γ) (Const-N x k)
    hnf' false Γ v@(Const-N x _)       = v
    hnf' true Γ v@(App b t t₁) with hnf' true Γ t | hnf' false Γ t₁
    ... | Cont n Γ' x | x₁             = log (pushTerm (proj₁ Γ , Γ') n x₁) v $ hnf' true (pushTerm (proj₁ Γ , Γ') n x₁) x
    ... | x           | x₁             = App b x x₁
    hnf' false Γ v@(App b t t₁)        = log Γ v $ App b (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' true  Γ v@(Lam-P b x t)       = log Γ v $ Cont x (proj₂ Γ) t
    hnf' false Γ v@(Lam-P b x t)       = log Γ v $ Lam-P b x (hnf' false (pushAbstract Γ x) t)
    hnf' b Γ (Cont _ _ _)              = error "Error in hnf'"
    hnf' b Γ (Pi b' x t t₁)            = Pi b' x (hnf' false Γ t) (hnf' false (pushAbstract Γ x) t₁)
    hnf' b Γ (Iota x t t₁)             = Iota x (hnf' false Γ t) (hnf' false (pushAbstract Γ x) t₁)
    hnf' b Γ (Eq-T t t₁)               = Eq-T (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' b Γ (M-T t)                   = M-T (hnf' false Γ t)
    hnf' b Γ (Mu t t₁)                 = Mu (hnf' false Γ t) (hnf' false Γ t₁)
    hnf' b Γ (Epsilon t)               = Epsilon (hnf' false Γ t)
    hnf' b Γ (Ev m x)                  = Ev m (mapPrimMetaArgs (hnf' false Γ) x)

  hnfExec = hnf' true
  open Conv hnfExec convDef using () renaming (nf to hnf') public

hnf    = hnf' false
hnfLog = hnf' true
