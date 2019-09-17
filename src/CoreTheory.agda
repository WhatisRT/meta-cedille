--------------------------------------------------------------------------------
-- This file provides the data structures and functions for the theory of
-- cedille core extended with the constructs for metaprogramming.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module CoreTheory where

import Agda.Builtin.Nat using (_+_; _-_; _==_)
import Data.Product
import Data.Word.Unsafe
open import Class.Map
open import Class.Monad.Except
open import Class.Monad.Profiler
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (length)
open import Data.Maybe using () renaming (map to mapMaybe)
open import Data.SimpleMap
open import Data.Word
open import Monads.Except
open import Relation.Nullary
open import Data.Word64.Exts

open import Prelude

data Sort : Set where
  ⋆ : Sort
  □ : Sort

instance
  Sort-Show : Show Sort
  Sort-Show = record { show = helper }
    where
      helper : Sort -> String
      helper ⋆ = "*"
      helper □ = "□"

  Sort-Eq : Eq Sort
  Sort-Eq = record { _≟_ = helper }
    where
      helper : (s s' : Sort) -> Dec (s ≡ s')
      helper ⋆ ⋆ = yes refl
      helper ⋆ □ = no λ ()
      helper □ ⋆ = no λ ()
      helper □ □ = yes refl

  Sort-EqB = Eq→EqB {{Sort-Eq}}

data GlobalName : Set where
  Global : String -> GlobalName

instance
  GlobalName-Eq : Eq GlobalName
  GlobalName-Eq = record { _≟_ = helper }
    where
      helper : (n n' : GlobalName) -> Dec (n ≡ n')
      helper (Global x) (Global x₁) with x ≟ x₁
      ... | yes p rewrite p = yes refl
      ... | no ¬p = no λ { refl -> ¬p refl }

  GlobalName-EqB : EqB GlobalName
  GlobalName-EqB = record { _≣_ = helper }
    where
      helper : (n n' : GlobalName) -> Bool
      helper (Global x) (Global x₁) = x ≣ x₁

  GlobalName-Show : Show GlobalName
  GlobalName-Show = record { show = helper }
    where
      helper : GlobalName -> String
      helper (Global x) = x

𝕀 : Set
𝕀 = Word64

instance
  𝕀-Eq : Eq 𝕀
  𝕀-Eq = record { _≟_ = Data.Word.Unsafe._≟_ }

  𝕀-EqB : EqB 𝕀
  𝕀-EqB = record { _≣_ = λ x y -> toℕ x Agda.Builtin.Nat.== toℕ y }

  𝕀-Show : Show 𝕀
  𝕀-Show = record { show = show ∘ toℕ }

_<𝕀_ : 𝕀 -> 𝕀 -> Bool
x <𝕀 y = (toℕ x) <ᵇ (toℕ y)

_+𝕀_ : 𝕀 -> 𝕀 -> 𝕀
x +𝕀 y = fromℕ ((toℕ x) Agda.Builtin.Nat.+ (toℕ y))

_-𝕀_ : 𝕀 -> 𝕀 -> 𝕀
_-𝕀_ = subWord

suc𝕀 : 𝕀 -> 𝕀
suc𝕀 = _+𝕀 (fromℕ 1)

pred𝕀 : 𝕀 -> 𝕀
pred𝕀 = _-𝕀 (fromℕ 1)

data Name : Set where
  Bound : 𝕀 -> Name
  Free : String -> Name

instance
  Name-Eq : Eq Name
  Name-Eq = record { _≟_ = helper }
    where
      helper : (n n' : Name) -> Dec (n ≡ n')
      helper (Bound x) (Bound x₁) with x ≟ x₁
      ... | yes p rewrite p = yes refl
      ... | no ¬p = no λ { refl -> ¬p refl }
      helper (Bound x) (Free x₁) = no λ ()
      helper (Free x) (Bound x₁) = no (λ ())
      helper (Free x) (Free x₁) with x ≟ x₁
      ... | yes p rewrite p = yes refl
      ... | no ¬p = no λ { refl -> ¬p refl }

  Name-EqB : EqB Name
  Name-EqB = record { _≣_ = helper }
    where
      helper : (n n' : Name) -> Bool
      helper (Bound x) (Bound x₁) = x ≣ x₁
      helper (Bound x) (Free x₁) = false
      helper (Free x) (Bound x₁) = false
      helper (Free x) (Free x₁) = x ≣ x₁

  Name-Show : Show Name
  Name-Show = record { show = helper }
    where
      helper : Name -> String
      helper (Bound x) = show x
      helper (Free x) = x

data PrimMeta : Set where
  EvalStmt : PrimMeta
  ShellCmd : PrimMeta
  CatchErr : PrimMeta

instance
  PrimMeta-Show : Show PrimMeta
  PrimMeta-Show = record { show = helper }
    where
      helper : PrimMeta -> String
      helper EvalStmt = "EvalStmt"
      helper ShellCmd = "ShellCmd"
      helper CatchErr = "CatchErr"

primMetaArgs : Set -> PrimMeta -> Set
primMetaArgs A EvalStmt = A
primMetaArgs A ShellCmd = A × A
primMetaArgs A CatchErr = A × A

mapPrimMetaArgs : ∀ {A B} -> (A -> B) -> {m : PrimMeta} -> primMetaArgs A m -> primMetaArgs B m
mapPrimMetaArgs f {EvalStmt} = f
mapPrimMetaArgs f {ShellCmd} = Data.Product.map f f
mapPrimMetaArgs f {CatchErr} = Data.Product.map f f

private
  traverseHomPair : ∀ {A B M} {{_ : Monad M}} -> (A -> M B) -> A × A -> M (B × B)
  traverseHomPair f (fst , snd) = do
    fst' <- f fst
    snd' <- f snd
    return (fst' , snd')

traversePrimMetaArgs : ∀ {A B M} {{_ : Monad M}}
                     -> (A -> M B) -> {m : PrimMeta} -> primMetaArgs A m -> M (primMetaArgs B m)
traversePrimMetaArgs f {EvalStmt} args = f args
traversePrimMetaArgs f {ShellCmd} = traverseHomPair f
traversePrimMetaArgs f {CatchErr} = traverseHomPair f

private
  showHomPair : ∀ {A} -> (A -> String) -> A × A -> String
  showHomPair showA (fst , snd) = showA fst + " " + showA snd

primMetaArgs-Show : ∀ {A} -> (A -> String) -> (m : PrimMeta) -> primMetaArgs A m -> String
primMetaArgs-Show showA EvalStmt args = showA args
primMetaArgs-Show showA ShellCmd = showHomPair showA
primMetaArgs-Show showA CatchErr = showHomPair showA

data PureTerm : Set where
  Var-P : Name -> PureTerm
  Sort-P : Sort -> PureTerm
  App-P : PureTerm -> PureTerm -> PureTerm
  Lam-P : PureTerm -> PureTerm
  Pi-P : PureTerm -> PureTerm -> PureTerm
  All-P : PureTerm -> PureTerm -> PureTerm
  Iota-P : PureTerm -> PureTerm -> PureTerm
  Eq-P : PureTerm -> PureTerm -> PureTerm
  M-P : PureTerm -> PureTerm
  Mu-P : PureTerm -> PureTerm -> PureTerm
  Epsilon-P : PureTerm -> PureTerm
  Ev-P : (m : PrimMeta) -> primMetaArgs PureTerm m -> PureTerm

instance
  {-# TERMINATING #-}
  PureTerm-Show : Show PureTerm
  PureTerm-Show = record { show = helper }
    where
      helper : PureTerm -> String
      helper (Var-P x) = show x
      helper (Sort-P x) = show x
      helper (App-P t t₁) = "[" + helper t + " " + helper t₁ + "]"
      helper (Lam-P t) = "λ " + helper t
      helper (Pi-P t t₁) = "Π " + helper t + " " + helper t₁
      helper (All-P t t₁) = "∀ " + helper t + " " + helper t₁
      helper (Iota-P t t₁) = "ι " + helper t + " " + helper t₁
      helper (Eq-P t t₁) = "= " + helper t + " " + helper t₁
      helper (M-P t) = "M " + helper t
      helper (Mu-P t t₁) = "μ " + helper t + " " + helper t₁
      helper (Epsilon-P t) = "ε " + helper t
      helper (Ev-P m args) = "ζ " + show m + " " + primMetaArgs-Show helper m args

pureTermBeq : {M : Set -> Set} {{_ : Monad M}} {{_ : MonadExcept M String}}
  -> PureTerm -> PureTerm -> M ⊤
pureTermBeq (Var-P x) (Var-P x₁) =
  if x ≣ x₁
    then return tt
    else throwError ("Name " + show x + " isn't equal to name " + show x₁)
pureTermBeq (Sort-P x) (Sort-P x₁) =
  if x ≣ x₁
    then return tt
    else throwError ("Sort " + show x + " isn't equal to sort " + show x₁)
pureTermBeq (App-P t t₁) (App-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Lam-P t) (Lam-P t₁) = pureTermBeq t t₁
pureTermBeq (Pi-P t t₁) (Pi-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (All-P t t₁) (All-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Iota-P t t₁) (Iota-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Eq-P t t₁) (Eq-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (M-P t) (M-P x) = pureTermBeq x t
pureTermBeq (Mu-P t t₁) (Mu-P x x₁) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Epsilon-P t) (Epsilon-P x) = pureTermBeq t x
pureTermBeq (Ev-P EvalStmt t) (Ev-P EvalStmt x) = pureTermBeq t x
pureTermBeq (Ev-P ShellCmd (t , t₁)) (Ev-P ShellCmd (x , x₁)) = pureTermBeq t x >> pureTermBeq t₁ x₁
pureTermBeq (Ev-P CatchErr (t , t₁)) (Ev-P CatchErr (x , x₁)) = pureTermBeq t x >> pureTermBeq t₁ x₁
{-# CATCHALL #-}
pureTermBeq t t' =
  throwError $ "The terms " + show t + " and " + show t' + " aren't equal!"

data AnnTerm : Set where
  Var-A : Name -> AnnTerm
  Sort-A : Sort -> AnnTerm
  _∙1 : AnnTerm -> AnnTerm
  _∙2 : AnnTerm -> AnnTerm
  β : AnnTerm -> AnnTerm -> AnnTerm -- proves first arg eq, erase to second arg
  δ : AnnTerm -> AnnTerm -> AnnTerm -- inhabits first arg if snd arg proves false
  ς : AnnTerm -> AnnTerm
  App-A : AnnTerm -> AnnTerm -> AnnTerm
  AppE-A : AnnTerm -> AnnTerm -> AnnTerm
  ρ_∶_-_ : AnnTerm -> AnnTerm -> AnnTerm -> AnnTerm -- first arg is eq, rewrite the name in the third arg and inhabit with fourth arg
  ∀-A : AnnTerm -> AnnTerm -> AnnTerm
  Π : AnnTerm -> AnnTerm -> AnnTerm
  ι : AnnTerm -> AnnTerm -> AnnTerm
  λ-A : AnnTerm -> AnnTerm -> AnnTerm
  Λ : AnnTerm -> AnnTerm -> AnnTerm
  [_,_∙_] : AnnTerm -> AnnTerm -> AnnTerm -> AnnTerm
  φ : AnnTerm -> AnnTerm -> AnnTerm -> AnnTerm
  -- there is a let binding here, which is probably unnecessary
  _≃_ : AnnTerm -> AnnTerm -> AnnTerm
  M-A : AnnTerm -> AnnTerm
  μ : AnnTerm -> AnnTerm -> AnnTerm
  ε : AnnTerm -> AnnTerm
  Ev-A : (x : PrimMeta) -> primMetaArgs AnnTerm x -> AnnTerm

instance
  {-# TERMINATING #-}
  AnnTerm-Show : Show AnnTerm
  AnnTerm-Show = record { show = helper }
    where
      helper : AnnTerm -> String
      helper (Var-A x) = show x
      helper (Sort-A x) = show x
      helper (t ∙1) = "π1 " + helper t
      helper (t ∙2) = "π2 " + helper t
      helper (β t t₁) = "β " + helper t + " " + helper t₁
      helper (δ t t₁) = "δ" + helper t + " " + helper t₁
      helper (ς t) = "ς" + helper t
      helper (App-A t t₁) = "[" + helper t + " " + helper t₁ + "]"
      helper (AppE-A t t₁) = "<" + helper t + " " + helper t₁ + ">"
      helper (ρ t ∶ t₁ - t₂) = "ρ " + helper t + " : " + helper t₁ + " " + helper t₂
      helper (∀-A t t₁) = "∀ " + helper t + " " + helper t₁
      helper (Π t t₁) = "Π " + helper t + " " + helper t₁
      helper (ι t t₁) = "ι " + helper t + " " + helper t₁
      helper (λ-A t t₁) = "λ " + helper t + " " + helper t₁
      helper (Λ t t₁) = "Λ " + helper t + " " + helper t₁
      helper [ t , t₁ ∙ t₂ ] = "{" + helper t + "," + helper t₁ + " . " + helper t₂ + "}"
      helper (φ t t₁ t₂) = "φ"
      helper (t ≃ t₁) = "(= " + helper t + " " + helper t₁ + ")"
      helper (M-A t) = "M " + helper t
      helper (μ t t₁) = "μ " + helper t + " " + helper t₁
      helper (ε t) = "ε " + helper t
      helper (Ev-A m args) = "Ev " + show m + " " + primMetaArgs-Show helper m args

annTermBeq : AnnTerm -> AnnTerm -> Bool
annTermBeq (Var-A x) (Var-A x₁) = x ≣ x₁
annTermBeq (Sort-A x) (Sort-A x₁) = x ≣ x₁
annTermBeq (t ∙1) (t₁ ∙1) = annTermBeq t t₁
annTermBeq (t ∙2) (t₁ ∙2) = annTermBeq t t₁
annTermBeq (β t t₁) (β u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (δ t t₁) (δ u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (ς t) (ς t₁) = annTermBeq t t₁
annTermBeq (App-A t t₁) (App-A u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (AppE-A t t₁) (AppE-A u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (ρ t ∶ t₁ - t₂) (ρ u ∶ u₁ - u₂) = annTermBeq t u ∧ annTermBeq t₁ u₁ ∧ annTermBeq t₂ u₂
annTermBeq (∀-A t t₁) (∀-A u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (Π t t₁) (Π u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (ι t t₁) (ι u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (λ-A t t₁) (λ-A u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (Λ t t₁) (Λ u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq [ t , t₁ ∙ t₂ ] [ u , u₁ ∙ u₂ ] = annTermBeq t u ∧ annTermBeq t₁ u₁ ∧ annTermBeq t₂ u₂
annTermBeq (φ t t₁ t₂) (φ u u₁ u₂) = annTermBeq t u ∧ annTermBeq t₁ u₁ ∧ annTermBeq t₂ u₂
annTermBeq (t ≃ t₁) (u ≃ u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (M-A t) (M-A u) = annTermBeq t u
annTermBeq (μ t t₁) (μ u u₁) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (ε t) (ε u) = annTermBeq t u
annTermBeq (Ev-A EvalStmt t) (Ev-A EvalStmt u) = annTermBeq t u
annTermBeq (Ev-A ShellCmd (t , t₁)) (Ev-A ShellCmd (u , u₁)) = annTermBeq t u ∧ annTermBeq t₁ u₁
annTermBeq (Ev-A CatchErr (t , t₁)) (Ev-A CatchErr (u , u₁)) = annTermBeq t u ∧ annTermBeq t₁ u₁
{-# CATCHALL #-}
annTermBeq _ _ = false

data Def : Set where
  Let : AnnTerm -> AnnTerm -> Def
  Axiom : AnnTerm -> Def

data EfficientDef : Set where
  EfficientLet : AnnTerm -> PureTerm -> AnnTerm -> EfficientDef
  EfficientAxiom : AnnTerm -> EfficientDef

toDef : EfficientDef -> Def
toDef (EfficientLet x x₁ x₂) = Let x x₂
toDef (EfficientAxiom x) = Axiom x

getNorm : EfficientDef -> Maybe PureTerm
getNorm (EfficientLet x x₁ x₂) = return x₁
getNorm (EfficientAxiom x) = nothing

instance
  Def-Show : Show Def
  Def-Show = record { show = helper }
    where
      helper : Def -> String
      helper (Let x x₁) = " := " + show x + " : " + show x₁
      helper (Axiom x) = " : " + show x

typeOfDef : Def -> AnnTerm
typeOfDef (Let x x₁) = x₁
typeOfDef (Axiom x) = x

{-# TERMINATING #-}
modifyIndicesPure : 𝕀 -> PureTerm -> PureTerm
modifyIndicesPure = helper (fromℕ 0)
  where
    helper : 𝕀 -> 𝕀 -> PureTerm -> PureTerm
    helper k n v@(Var-P (Bound x)) = if x <𝕀 k then v else Var-P (Bound $ pred𝕀 (x +𝕀 n))
    helper k n v@(Var-P (Free x)) = v
    helper k n v@(Sort-P x) = v
    helper k n (App-P t t₁) = App-P (helper k n t) (helper k n t₁)
    helper k n (Lam-P t) = Lam-P (helper (suc𝕀 k) n t)
    helper k n (Pi-P t t₁) = Pi-P (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (All-P t t₁) = All-P (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Iota-P t t₁) = Iota-P (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Eq-P t t₁) = Eq-P (helper k n t) (helper k n t₁)
    helper k n (M-P t) = M-P (helper k n t)
    helper k n (Mu-P t t₁) = Mu-P (helper k n t) (helper k n t₁)
    helper k n (Epsilon-P t) = Epsilon-P (helper k n t)
    helper k n (Ev-P m args) = Ev-P m (mapPrimMetaArgs (helper k n) args)

incrementIndicesPureBy : 𝕀 -> PureTerm -> PureTerm
incrementIndicesPureBy i = modifyIndicesPure (suc𝕀 i)

decrementIndicesPure : PureTerm -> PureTerm
decrementIndicesPure = modifyIndicesPure (fromℕ 0)

{-# TERMINATING #-}
modifyIndices : 𝕀 -> AnnTerm -> AnnTerm
modifyIndices = helper (fromℕ 0)
  where
    helper : 𝕀 -> 𝕀 -> AnnTerm -> AnnTerm
    helper k n v@(Var-A (Bound x)) = if x <𝕀 k then v else Var-A (Bound $ pred𝕀 (x +𝕀 n))
    helper k n v@(Var-A (Free x)) = v
    helper k n (Sort-A x) = Sort-A x
    helper k n (t ∙1) = helper k n t ∙1
    helper k n (t ∙2) = helper k n t ∙2
    helper k n (β t t₁) = β (helper k n t) (helper k n t₁)
    helper k n (δ t t₁) = δ (helper k n t) (helper k n t₁)
    helper k n (ς t) = ς (helper k n t)
    helper k n (App-A t t₁) = App-A (helper k n t) (helper k n t₁)
    helper k n (AppE-A t t₁) = AppE-A (helper k n t) (helper k n t₁)
    helper k n (ρ t ∶ t₁ - t₂) = ρ (helper k n t) ∶ (helper (suc𝕀 k) n t₁) - (helper k n t₂)
    helper k n (∀-A t t₁) = ∀-A (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Π t t₁) = Π (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (ι t t₁) = ι (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (λ-A t t₁) = λ-A (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n (Λ t t₁) = Λ (helper k n t) (helper (suc𝕀 k) n t₁)
    helper k n [ t , t₁ ∙ t₂ ] = [ (helper k n t) , (helper k n t₁) ∙ (helper (suc𝕀 k) n t₂) ]
    helper k n (φ t t₁ t₂) = φ (helper k n t) (helper k n t₁) (helper k n t₂)
    helper k n (t ≃ t₁) = helper k n t ≃ helper k n t₁
    helper k n (M-A t) = M-A (helper k n t)
    helper k n (μ t t₁) = μ (helper k n t) (helper k n t₁)
    helper k n (ε t) = ε (helper k n t)
    helper k n (Ev-A m args) = Ev-A m (mapPrimMetaArgs (helper k n) args)

incrementIndicesBy : 𝕀 -> AnnTerm -> AnnTerm
incrementIndicesBy i = modifyIndices (suc𝕀 i)

decrementIndices : AnnTerm -> AnnTerm
decrementIndices = modifyIndices (fromℕ 0)

checkFree : Name -> PureTerm -> Bool
checkFree = helper 0
  where
    helper : ℕ -> Name -> PureTerm -> Bool
    helper k n (Var-P (Bound x)) = case n of λ
      { (Bound x₁) → x ≣ (fromℕ k +𝕀 x₁)
      ; (Free x₁) → false }
    helper k n (Var-P (Free x)) = case n of λ
      { (Bound x₁) → false
      ; (Free x₁) → x ≣ x₁ }
    helper k n (Sort-P x) = false
    helper k n (App-P t t₁) = helper k n t ∧ helper k n t₁
    helper k n (Lam-P t) = helper (suc k) n t
    helper k n (Pi-P t t₁) = helper k n t ∧ helper (suc k) n t₁
    helper k n (All-P t t₁) = helper k n t ∧ helper (suc k) n t₁
    helper k n (Iota-P t t₁) = helper k n t ∧ helper (suc k) n t₁
    helper k n (Eq-P t t₁) = helper k n t ∧ helper k n t₁
    helper k n (M-P t) = helper k n t
    helper k n (Mu-P t t₁) = helper k n t ∧ helper k n t₁
    helper k n (Epsilon-P t) = helper k n t
    helper k n (Ev-P EvalStmt t) = helper k n t
    helper k n (Ev-P ShellCmd (t , t₁)) = helper k n t ∧ helper k n t₁
    helper k n (Ev-P CatchErr (t , t₁)) = helper k n t ∧ helper k n t₁

GlobalContext : Set
GlobalContext = SimpleMap GlobalName EfficientDef -- TODO: go for something more efficient later

Context : Set
Context = GlobalContext × List AnnTerm

instance
  Context-Show : Show Context
  Context-Show = record { show = helper }
    where
      helper : Context -> String
      helper (fst , snd) =
        (show $ length snd) + " local variables:" + show snd

globalToContext : GlobalContext -> Context
globalToContext Γ = Γ , []

contextToGlobal : Context -> GlobalContext
contextToGlobal (fst , snd) = fst

-- add variable to context, so that index 0 points to that variable
pushVar : AnnTerm -> Context -> Context
pushVar v (fst , snd) = fst , v ∷ snd

localContextLength : Context -> ℕ
localContextLength (fst , snd) = length snd

efficientLookupInContext : Name -> Context -> Maybe EfficientDef
efficientLookupInContext (Bound x) (fst , snd) =
  Data.Maybe.map (λ y → EfficientAxiom (incrementIndicesBy (suc𝕀 x) y)) (lookupMaybe (toℕ x) snd)
efficientLookupInContext (Free x) (fst , snd) = lookup (Global x) fst

lookupInContext : Name -> Context -> Maybe Def
lookupInContext n Γ = mmap toDef $ efficientLookupInContext n Γ

validInContext : PureTerm -> Context -> Bool
validInContext = helper 0
  where
    -- instead of modifying the context here, we just count how many variables we would have added if we did
    helper : ℕ -> PureTerm -> Context -> Bool
    helper k (Var-P (Bound x)) Γ = x <𝕀 fromℕ (localContextLength Γ + k)
    helper k (Var-P n@(Free x)) Γ = maybe (λ _ → true) false $ lookupInContext n Γ
    helper k (Sort-P x) Γ = true
    helper k (App-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Lam-P t) Γ = helper (suc k) t Γ
    helper k (Pi-P t t₁) Γ = helper k t Γ ∧ helper (suc k) t₁ Γ
    helper k (All-P t t₁) Γ = helper k t Γ ∧ helper (suc k) t₁ Γ
    helper k (Iota-P t t₁) Γ = helper k t Γ ∧ helper (suc k) t₁ Γ
    helper k (Eq-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (M-P t) Γ = helper k t Γ
    helper k (Mu-P t t₁) Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Epsilon-P t) Γ = helper k t Γ
    helper k (Ev-P EvalStmt t) Γ = helper k t Γ
    helper k (Ev-P ShellCmd (t , t₁)) Γ = helper k t Γ ∧ helper k t₁ Γ
    helper k (Ev-P CatchErr (t , t₁)) Γ = helper k t Γ ∧ helper k t₁ Γ

{-# TERMINATING #-}
Erase : AnnTerm -> PureTerm
Erase (Var-A x) = Var-P x
Erase (Sort-A x) = Sort-P x
Erase (t ∙1) = Erase t
Erase (t ∙2) = Erase t
Erase (β t t₁) = Erase t₁
Erase (δ t t₁) = Erase t₁
Erase (ς t) = Erase t
Erase (App-A t t₁) = App-P (Erase t) (Erase t₁)
Erase (AppE-A t t₁) = Erase t
Erase (ρ t ∶ t₁ - t₂) = Erase t₂
Erase (∀-A t t₁) = All-P (Erase t) (Erase t₁)
Erase (Π t t₁) = Pi-P (Erase t) (Erase t₁)
Erase (ι t t₁) = Iota-P (Erase t) (Erase t₁)
Erase (λ-A t t₁) = Lam-P (Erase t₁)
Erase (Λ t t₁) = decrementIndicesPure (Erase t₁)
Erase ([_,_∙_] t t₁ t₂) = Erase t
Erase (φ t t₁ t₂) = Erase t₂
Erase (x ≃ x₁) = Eq-P (Erase x) (Erase x₁)
Erase (M-A t) = M-P (Erase t)
Erase (μ t t₁) = Mu-P (Erase t) (Erase t₁)
Erase (ε t) = Epsilon-P (Erase t)
Erase (Ev-A m args) = Ev-P m (mapPrimMetaArgs Erase args)

-- substitute the first unbound variable in t with t'
subst : AnnTerm -> AnnTerm -> AnnTerm
subst t t' = decrementIndices $ substIndex t (fromℕ 0) t'
  where
    -- substitute the k-th unbound variable in t with t'
    substIndex : AnnTerm -> 𝕀 -> AnnTerm -> AnnTerm
    substIndex v@(Var-A (Bound x)) k t' = if k ≣ x then incrementIndicesBy (suc𝕀 k) t' else v
    substIndex v@(Var-A (Free x)) k t' = v
    substIndex v@(Sort-A x) k t' = v
    substIndex (t ∙1) k t' = (substIndex t k t') ∙1
    substIndex (t ∙2) k t' = (substIndex t k t') ∙2
    substIndex (β t t₁) k t' = β (substIndex t k t') (substIndex t₁ k t')
    substIndex (δ t t₁) k t' = δ (substIndex t k t') (substIndex t₁ k t')
    substIndex (ς t) k t' = ς (substIndex t k t')
    substIndex (App-A t t₁) k t' = App-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (AppE-A t t₁) k t' = AppE-A (substIndex t k t') (substIndex t₁ k t')
    substIndex (ρ t ∶ t₁ - t₂) k t' = ρ (substIndex t k t') ∶ (substIndex t₁ k t') - (substIndex t₂ k t')
    substIndex (∀-A t t₁) k t' = ∀-A (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (Π t t₁) k t' = Π (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (ι t t₁) k t' = ι (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (λ-A t t₁) k t' = λ-A (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex (Λ t t₁) k t' = Λ (substIndex t k t') (substIndex t₁ (suc𝕀 k) t')
    substIndex [ t , t₁ ∙ t₂ ] k t' = [ (substIndex t k t') , (substIndex t₁ k t') ∙ substIndex t₂ (suc𝕀 k) t' ]
    substIndex (φ t t₁ t₂) k t' = φ (substIndex t k t') (substIndex t₁ k t') (substIndex t₂ k t')
    substIndex (t ≃ t₁) k t' = substIndex t k t' ≃ substIndex t₁ k t'
    substIndex (M-A t) k t' = M-A (substIndex t k t')
    substIndex (μ t t₁) k t' = μ (substIndex t k t') (substIndex t₁ k t')
    substIndex (ε t) k t' = ε (substIndex t k t')
    substIndex (Ev-A EvalStmt t) k t' = Ev-A EvalStmt (substIndex t k t')
    substIndex (Ev-A ShellCmd (t , t₁)) k t' = Ev-A ShellCmd ((substIndex t k t' , substIndex t₁ k t'))
    substIndex (Ev-A CatchErr (t , t₁)) k t' = Ev-A CatchErr ((substIndex t k t' , substIndex t₁ k t'))

-- substitute the first unbound variable in t with t'
substPure : PureTerm -> PureTerm -> PureTerm
substPure t t' = decrementIndicesPure $ substIndexPure t (fromℕ 0) t'
  where
    -- substitute the k-th unbound variable in t with t'
    substIndexPure : PureTerm -> 𝕀 -> PureTerm -> PureTerm
    substIndexPure v@(Var-P (Bound x)) k t' = if k ≣ x then incrementIndicesPureBy (suc𝕀 k) t' else v
    substIndexPure v@(Var-P (Free x)) k t' = v
    substIndexPure v@(Sort-P x) k t' = v
    substIndexPure (App-P t t₁) k t' = App-P (substIndexPure t k t') (substIndexPure t₁ k t')
    substIndexPure (Lam-P t) k t' = Lam-P (substIndexPure t (suc𝕀 k) t')
    substIndexPure (Pi-P t t₁) k t' = Pi-P (substIndexPure t k t') (substIndexPure t₁ (suc𝕀 k) t')
    substIndexPure (All-P t t₁) k t' = All-P (substIndexPure t k t') (substIndexPure t₁ (suc𝕀 k) t')
    substIndexPure (Iota-P t t₁) k t' = Iota-P (substIndexPure t k t') (substIndexPure t₁ (suc𝕀 k) t')
    substIndexPure (Eq-P t t₁) k t' = Eq-P (substIndexPure t k t') (substIndexPure t₁ k t')
    substIndexPure (M-P t) k t' = M-P (substIndexPure t k t')
    substIndexPure (Mu-P t t₁) k t' = Mu-P (substIndexPure t k t') (substIndexPure t₁ k t')
    substIndexPure (Epsilon-P t) k t' = Epsilon-P (substIndexPure t k t')
    substIndexPure (Ev-P EvalStmt t) k t' = Ev-P EvalStmt (substIndexPure t k t')
    substIndexPure (Ev-P ShellCmd (t , t₁)) k t' = Ev-P ShellCmd ((substIndexPure t k t' , substIndexPure t₁ k t'))
    substIndexPure (Ev-P CatchErr (t , t₁)) k t' = Ev-P CatchErr ((substIndexPure t k t' , substIndexPure t₁ k t'))

stripBinder : AnnTerm -> Maybe AnnTerm
stripBinder (∀-A t' t'') = just t''
stripBinder (Π t' t'') = just t''
stripBinder (ι t' t'') = just t''
stripBinder (λ-A t' t'') = just t''
stripBinder (Λ t' t'') = just t''
{-# CATCHALL #-}
stripBinder t = nothing

-- something in is head normal form, if its outermost constructor is not one of the following: Var-A (if the lookup fails), App-A, AppE-A
{-# TERMINATING #-}
hnfNorm : Context -> AnnTerm -> AnnTerm
hnfNorm Γ (Var-A x) with lookupInContext x Γ
hnfNorm Γ (Var-A x) | just (Let x₁ x₂) = hnfNorm Γ x₁
hnfNorm Γ v@(Var-A x) | just (Axiom x₁) = v -- we cannot reduce axioms
hnfNorm Γ v@(Var-A x) | nothing = v -- in case the lookup fails, we cannot reduce
hnfNorm Γ (App-A t t₁) = maybe (λ t' -> hnfNorm Γ $ subst t' t₁) (App-A t t₁) $ stripBinder (hnfNorm Γ t)
hnfNorm Γ (AppE-A t t₁) = maybe (λ t' -> hnfNorm Γ $ subst t' t₁) (App-A t t₁) $ stripBinder (hnfNorm Γ t)
{-# CATCHALL #-}
hnfNorm Γ v = v

stripBinderPure : PureTerm -> Maybe PureTerm
stripBinderPure (Lam-P t') = just t'
stripBinderPure (Pi-P t' t'') = just t''
stripBinderPure (All-P t' t'') = just t''
stripBinderPure (Iota-P t' t'') = just t''
{-# CATCHALL #-}
stripBinderPure _ = nothing

hnfNormPure : Context -> PureTerm -> PureTerm
{-# NON_TERMINATING #-}
hnfNormPure Γ (Var-P x) with lookupInContext x Γ
hnfNormPure Γ (Var-P x) | just (Let x₁ x₂) = hnfNormPure Γ $ Erase x₁
hnfNormPure Γ v@(Var-P x) | just (Axiom x₁) = v -- we cannot reduce axioms
hnfNormPure Γ v@(Var-P x) | nothing = v -- in case the lookup fails, we cannot reduce
hnfNormPure Γ (App-P t t₁) = case stripBinderPure (hnfNormPure Γ t) of λ
  { (just t') → hnfNormPure Γ $ substPure t' t₁
  ; nothing → App-P t t₁ }
{-# CATCHALL #-}
hnfNormPure Γ v = v

{-# TERMINATING #-}
findOutermostConstructor : PureTerm -> PureTerm × List PureTerm
findOutermostConstructor t = outermostApp $ stripBinders t
  where
    stripBinders : PureTerm -> PureTerm
    stripBinders t with stripBinderPure t
    stripBinders t | just x = stripBinders x
    stripBinders t | nothing = t

    outermostApp : PureTerm -> PureTerm × List PureTerm
    outermostApp (App-P t t₁) = Data.Product.map id (t₁ ∷_) $ outermostApp t
    {-# CATCHALL #-}
    outermostApp t = t , []

{-# NON_TERMINATING #-}
normalizePure : Context -> PureTerm -> PureTerm
normalizePure Γ (Var-P x) with efficientLookupInContext x Γ
normalizePure Γ (Var-P x) | just (EfficientLet x₁ x₂ x₃) = x₂
normalizePure Γ v@(Var-P x) | just (EfficientAxiom x₁) = v -- we cannot reduce axioms
normalizePure Γ v@(Var-P x) | nothing = v -- in case the lookup fails, we cannot reduce
normalizePure Γ v@(Sort-P x) = v
normalizePure Γ (App-P t t₁) = case hnfNormPure Γ t of λ t' ->
  case stripBinderPure t' of λ
    { (just t'') → normalizePure Γ (substPure t'' t₁)
    ; nothing → App-P (normalizePure Γ t) (normalizePure Γ t₁) }
normalizePure Γ (Lam-P t) = case normalizePure Γ t of λ
  { t''@(App-P t' (Var-P (Bound i))) -> if i ≣ (fromℕ 0) ∧ validInContext t' Γ then decrementIndicesPure t' else Lam-P t'' -- eta reduce here
  ; t'' -> Lam-P t'' }
normalizePure Γ (Pi-P t t₁) = Pi-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (All-P t t₁) = All-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Iota-P t t₁) = Iota-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Eq-P t t₁) = Eq-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (M-P t) = M-P (normalizePure Γ t)
normalizePure Γ (Mu-P t t₁) = Mu-P (normalizePure Γ t) (normalizePure Γ t₁)
normalizePure Γ (Epsilon-P t) = Epsilon-P (normalizePure Γ t)
normalizePure Γ (Ev-P m args) = Ev-P m (mapPrimMetaArgs (normalizePure Γ) args)

insertInGlobalContext : GlobalName -> Def -> GlobalContext -> String ⊎ GlobalContext
insertInGlobalContext n d Γ =
  if is-just $ lookup n Γ
    then inj₁ ("The name " + show n + " is already defined!")
    else (inj₂ $ insert n (toEfficientDef d Γ) Γ)
  where
    toEfficientDef : Def -> GlobalContext -> EfficientDef
    toEfficientDef (Let x x₁) Γ = EfficientLet x (normalizePure (globalToContext Γ) $ Erase x) x₁
    toEfficientDef (Axiom x) Γ = EfficientAxiom x

module CheckEquality {M : Set -> Set} {{_ : Monad M}} {{_ : MonadExcept M String}} (Γ : Context) where

  compareNames : PureTerm -> PureTerm -> M ⊤
  compareNames (Var-P x) (Var-P x₁) =
    if x ≣ x₁
      then return tt
      else throwError "Names not equal! If you see this message, this is a bug!"
  {-# CATCHALL #-}
  compareNames _ _ = throwError "Terms are not names! If you see this message, this is a bug!"

  {-# NON_TERMINATING #-}
  checkβηPure : PureTerm -> PureTerm -> M ⊤
  checkβηPure t t' =
    tryElse (compareNames t t') $
    compareHnfs (hnfNormPure Γ t) (hnfNormPure Γ t')
    -- tryElse (compareHnfs (hnfNormPure Γ t) (hnfNormPure Γ t')) $
    -- pureTermBeq t t'
    where
      hnfError : PureTerm -> PureTerm -> M ⊤
      hnfError t t' =
        throwError $ "The terms " + show t + " and " + show t' + " aren't equal!"

      compareHnfs : PureTerm -> PureTerm -> M ⊤
      compareHnfs (Var-P x) (Var-P x₁) =
        if x ≣ x₁
          then return tt
          else throwError ("Name " + show x + " isn't equal to name " + show x₁)
      compareHnfs (Sort-P x) (Sort-P x₁) =
        if x ≣ x₁
          then return tt
          else throwError ("Sort " + show x + " isn't equal to sort " + show x₁)
      compareHnfs (App-P t t₁) (App-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Lam-P t) (Lam-P t₁) = checkβηPure t t₁
      compareHnfs (Pi-P t t₁) (Pi-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (All-P t t₁) (All-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Iota-P t t₁) (Iota-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Eq-P t t₁) (Eq-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (M-P t) (M-P x) = checkβηPure x t
      compareHnfs (Mu-P t t₁) (Mu-P x x₁) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Epsilon-P t) (Epsilon-P x) = checkβηPure t x
      compareHnfs (Ev-P EvalStmt t) (Ev-P EvalStmt x) = checkβηPure t x
      compareHnfs (Ev-P ShellCmd (t , t₁)) (Ev-P ShellCmd (x , x₁)) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Ev-P CatchErr (t , t₁)) (Ev-P CatchErr (x , x₁)) = checkβηPure t x >> checkβηPure t₁ x₁
      compareHnfs (Lam-P t) t₁ = case normalizePure Γ t of λ
        { t''@(App-P t' (Var-P (Bound i))) ->
          if i ≣ (fromℕ 0) ∧ validInContext t' Γ then (compareHnfs (decrementIndicesPure t') t₁) else hnfError t'' t₁
        ; t'' -> hnfError t'' t₁ }
      compareHnfs t (Lam-P t₁) = case normalizePure Γ t₁ of λ
        { t''@(App-P t' (Var-P (Bound i))) ->
          if i ≣ (fromℕ 0) ∧ validInContext t' Γ then (compareHnfs t (decrementIndicesPure t')) else hnfError t t''
        ; t'' -> hnfError t t'' }
      {-# CATCHALL #-}
      compareHnfs t t' = hnfError t t'

  checkβη : AnnTerm -> AnnTerm -> M ⊤
  checkβη t t' = checkβηPure (Erase t) (Erase t')

open CheckEquality public

{-# TERMINATING #-}
synthType :
  {M : Set -> Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadProfiler M (String × (List String))}}
  -> Context -> AnnTerm -> M AnnTerm
synthType' :
  {M : Set -> Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadProfiler M (String × (List String))}}
  -> Context -> AnnTerm -> M AnnTerm

synthType Γ t =
  appendIfError
    (synthType' Γ t)
    ("\n\nWhile synthesizing type for " + show t + " in context:\n" + show {{Context-Show}} Γ)

synthType' Γ (Var-A x) =
  maybeToError
    (mapMaybe typeOfDef $ lookupInContext x Γ)
    ("Lookup failed: " + show x + " in context " + show {{Context-Show}} Γ)
synthType' Γ (Sort-A ⋆) = return $ Sort-A □
synthType' Γ (Sort-A □) = throwError "Cannot synthesize type for the superkind"

synthType' Γ (t ∙1) = do
  T <- synthType Γ t
  case (hnfNorm Γ T) of λ
    { (ι u u₁) → return u
    ; _ -> throwError "Term does not normalize to an iota term" }

synthType' Γ (t ∙2) = do
  T <- synthType Γ t
  case (hnfNorm Γ T) of λ
    { (ι u u₁) → return $ subst u₁ (t ∙1)
    ; _ -> throwError "Term does not normalize to an iota term" }

synthType' Γ (β t t₁) = do
  T <- synthType Γ (t ≃ t)
  case (hnfNorm Γ T) of λ
    { (Sort-A ⋆) -> return $ t ≃ t
    ; _ -> throwError "Equality type does not have the right type. Is this a bug?" }

synthType' Γ (δ t t₁) = do
  T <- synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (u ≃ u₁) -> do
      catchError
        (pureTermBeq (normalizePure Γ $ Erase u) (Lam-P $ Lam-P (Var-P $ Bound (fromℕ 1))) >>
         pureTermBeq (normalizePure Γ $ Erase u₁) (Lam-P $ Lam-P (Var-P $ Bound (fromℕ 0))))
        (λ e -> throwError $
          "This equality cannot be used for the delta term: " + show u
          + " = " + show u₁ + "\nError: " + e)
      return t
    ; _ -> throwError "The second argument of a delta needs to be of an eq type" }

synthType' Γ (ς t) = do
  T <- synthType Γ t
  case (hnfNorm Γ T) of λ
    { (u ≃ u₁) -> return $ u₁ ≃ u
    ; _ -> throwError "Sigma needs an inhabitant of an eq type as argument" }

synthType' Γ (App-A t t₁) = do
  T <- synthType Γ t
  T₁ <- synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (Π u u₁) -> do
      catchError
        (checkβη Γ T₁ u)
        (λ e -> throwError ("Type mismatch in application, the type of " + show t₁
          + " : " + show T₁ +  " is not βη-equivalent to " + show u + "\nError: " + e))
      return $ subst u₁ t₁
    ; v -> throwError $
      "The left term in an application needs to have a pi type, while it has type " + show v }

synthType' Γ (AppE-A t t₁) = do
  T <- synthType Γ t
  T₁ <- synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (∀-A u u₁) -> do
      catchError (checkβη Γ u T₁)
        (λ e -> throwError
          ("Type mismatch in erased application, the following types are not βη-equivalent:\n"
            + show u + "\n" + show T₁ + "\nError:\n" + e))
      return $ subst u₁ t₁
    ; v -> throwError $
      "The left term in an erased application needs to have a forall type, while it has type "
        + show v + "\nTest: " + show T }

synthType' Γ (ρ t ∶ t₁ - t₂) = do
  T <- synthType Γ t
  T₁ <- synthType Γ t₂
  case (hnfNorm Γ T) of λ
    { (u ≃ u₁) -> do
      catchError (checkβη Γ (subst t₁ u₁) T₁)
        (λ e -> throwError $ "Type mismatch in rho: " + show (subst t₁ u₁)
          + " should be βη-equivalent to the synthesized type of " + show t₂ + " : "
          + show T₁ + "\nError:\n" + e)
      return $ subst t₁ u
    ; _ -> throwError "The type of the first argument of a rho needs to be an equality" }

synthType' Γ (∀-A t t₁) = do
  u <- synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-A s) -> do
      let Γ' = pushVar t Γ
      u₁ <- synthType Γ' t₁
      case (hnfNorm Γ' u₁) of λ
        { (Sort-A ⋆) -> return $ Sort-A ⋆
        ; v -> throwError $
          "The type family in forall should have type star, while it has type "
          + show v + " (" + show t₁ + ")\nContext: " + show {{Context-Show}} Γ' }
    ; _ -> throwError "The type of the parameter type in forall should be star or square" }

synthType' Γ (Π t t₁) = do
  u <- synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-A s) -> do
      let Γ' = pushVar t Γ
      u₁ <- synthType Γ' t₁
      case (hnfNorm Γ u₁) of λ
        { (Sort-A s') -> return $ Sort-A s'
        ; v -> throwError $
          "The type family in pi should have type star or square, while it has type " + show v }
    ; _ -> throwError "The type of the parameter type in pi should be star or square" }

synthType' Γ (ι t t₁) = do
  u <- synthType Γ t
  case (hnfNorm Γ u) of λ
    { (Sort-A ⋆) -> do
      let Γ' = pushVar t Γ
      u₁ <- synthType Γ' t₁
      case (hnfNorm Γ' u₁) of λ
        { (Sort-A ⋆) -> return $ Sort-A ⋆
        ; _ -> throwError "The type family in iota should have type star"}
    ; _ -> throwError "The type of the parameter type in iota should be star" }

synthType' Γ (λ-A t t₁) = profileCall ("Lambda" , []) $ do
  profileCall ("CheckType" , [ show t ]) $ synthType Γ t
  u <- profileCall ("CheckExpr" , [ show t₁ ]) $ synthType (pushVar t Γ) t₁
  return (Π t u)

synthType' Γ (Λ t t₁) =
  if checkFree (Bound (fromℕ 0)) (Erase t₁)
    then throwError "Erased arguments cannot appear bound in a term"
    else do
      synthType Γ t
      u <- synthType (pushVar t Γ) t₁
      return $ ∀-A t u

synthType' Γ ([_,_∙_] t t₁ t₂) = do
  catchError (checkβη Γ t t₁)
    (λ e -> throwError $
      "The terms in dependent intersection introduction have to be βη-equivalent. They normalize to:\n"
        + show (normalizePure Γ $ Erase t) + "\n"
        + show (normalizePure Γ $ Erase t₁) + "\nError:\n" + e)
  u <- synthType Γ t
  u₁ <- synthType Γ t₁
  catchError
    (checkβη Γ (subst t₂ t) u₁)
    (λ e -> throwError
      ("Type mismatch in the second argument of the dependent intersection: "
        + show (subst t₂ t) + " should be βη-equivalent to the synthesized type "
        + show u₁ + "\n" + e))
  let res = ι u t₂
  u₂ <- synthType Γ res
  case (hnfNorm Γ u₂) of λ
    { (Sort-A ⋆) -> return res
    ; _ -> throwError
      "The resulting iota type of the dependent intersection doesn't have type star. Is this a Bug?" }

synthType' Γ (φ t t₁ t₂) = do
  T <- synthType Γ t
  case (hnfNorm Γ T) of λ
    { (u ≃ u₁) -> do
      catchError
        (checkβη Γ t₁ u >> checkβη Γ t₂ u₁)
        (λ e -> throwError $
          "The arguments to phi are not equivalent to the sides of the equality. Error:\n" + e)
      synthType Γ t₁
    ; _ -> throwError "The first argument to phi should be of an equality type" }

synthType' Γ (x ≃ x₁) =
  if validInContext (Erase x) Γ
    then if validInContext (Erase x₁) Γ
      then return $ Sort-A ⋆
      else throwError
        ("The right term in the equality type needs to be valid in the context: " + show x₁)
    else throwError
      ("The left term in the equality type needs to be valid in the context: " + show x)

synthType' Γ (M-A t) = do
  T <- synthType Γ t
  case (hnfNorm Γ T) of λ
    { (Sort-A ∗) -> return $ Sort-A ∗
    ; _ -> throwError "The term M is applied to should have type ∗"}

synthType' Γ (μ t t₁) = do
  T <- synthType Γ t
  T' <- synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (M-A u) ->
      case (hnfNorm Γ T') of λ
        { (Π v v₁) -> do
          T'' <- if checkFree (Bound (fromℕ 0)) (Erase v₁)
            then throwError ("Index 0 is not allowed to appear in " + show v₁)
            else synthType (pushVar v Γ) v₁
          case (hnfNorm Γ T'') of λ
            { (Sort-A ∗) ->
              case (hnfNorm Γ v₁) of λ
                { (M-A v₂) ->
                  appendIfError
                    (checkβη Γ u v)
                    "The types in μ need to be compatible" >> return (M-A $ decrementIndices v₂)
                ; _ -> throwError
                  "The second term in a μ needs to have a Pi type that maps to 'M t' for some 't'" }
            ; _ -> throwError "The second term in a μ needs to have a non-dependent Pi type" }
        ; _ -> throwError "The second term in a μ needs to have a Pi type" }
    ; _ -> throwError "The first term in a μ needs to have type 'M t' for some 't'" }

synthType' Γ (ε t) = do
  T <- synthType Γ t
  return $ M-A T

synthType' Γ (Ev-A EvalStmt t) = do
  T <- synthType Γ t
  appendIfError
    (checkβη Γ T (Var-A $ Free "init$stmt"))
    "The term supplied to EvalStmt needs to be of type 'init$stmt'"
  return $ M-A (Var-A $ Free "init$metaResult")

synthType' Γ (Ev-A ShellCmd (t , t₁)) = do
  T <- synthType Γ t
  T₁ <- synthType Γ t₁
  appendIfError
    (checkβη Γ T (Var-A $ Free "init$string"))
    "The first term supplied to ShellCmd needs to be of type 'init$string'"
  appendIfError
    (checkβη Γ T₁ (Var-A $ Free "init$stringList"))
    "The second term supplied to ShellCmd needs to be of type 'init$stringList'"
  return $ M-A (Var-A $ Free "init$string")

synthType' Γ (Ev-A CatchErr (t , t₁)) = do
  T <- synthType Γ t
  T₁ <- synthType Γ t₁
  case (hnfNorm Γ T) of λ
    { (M-A u) -> do
      appendIfError (checkβη Γ T₁ (Π (Var-A $ Free "init$err") (incrementIndicesBy (fromℕ 1) $ M-A u)))
        ("The second term supplied to CatchErr has type " + show T₁ +
         ", while it should have type 'init$err -> M " + show u)
      return $ M-A u
    ; _ -> throwError "The first term in CatchErr needs to have type 'M t' for some 't'" }
