{-# OPTIONS --type-in-type #-}

import Data.Vec.Recursive
import Data.Vec.Recursive.Categorical
open import Class.Listable
open import Data.List.Relation.Unary.Any
open import Data.Fin using (toℕ)

open import Prelude
open import Prelude.Nat
open import Theory.TermLike
open import Theory.Names

module Theory.PrimMeta where

private
  variable
    A B C : Set
    M : Set → Set

data PrimMeta : Set where
  Let           : PrimMeta
  AnnLet        : PrimMeta
  SetEval       : PrimMeta
  ShellCmd      : PrimMeta
  CheckTerm     : PrimMeta
  Parse         : PrimMeta
  Normalize     : PrimMeta
  HeadNormalize : PrimMeta
  InferType     : PrimMeta
  Import        : PrimMeta
  GetEval       : PrimMeta
  Print         : PrimMeta
  WriteFile     : PrimMeta
  CommandLine   : PrimMeta
  SetDebug      : PrimMeta

private
  variable
    m : PrimMeta

instance
  PrimMeta-Listable : Listable PrimMeta
  PrimMeta-Listable = record
    { listing = Let ∷ AnnLet ∷ SetEval ∷ ShellCmd ∷ CheckTerm ∷ Parse ∷ Normalize ∷ HeadNormalize ∷ InferType ∷ Import ∷ GetEval ∷ Print ∷ WriteFile ∷ CommandLine ∷ SetDebug ∷ []
    ; complete = λ where
        Let           → pf 0 (here refl)
        AnnLet        → pf 1 (here refl)
        SetEval       → pf 2 (here refl)
        ShellCmd      → pf 3 (here refl)
        CheckTerm     → pf 4 (here refl)
        Parse         → pf 5 (here refl)
        Normalize     → pf 6 (here refl)
        HeadNormalize → pf 7 (here refl)
        InferType     → pf 8 (here refl)
        Import        → pf 9 (here refl)
        GetEval       → pf 10 (here refl)
        Print         → pf 11 (here refl)
        WriteFile     → pf 12 (here refl)
        CommandLine   → pf 13 (here refl)
        SetDebug      → pf 14 (here refl)
    }
    where pf = listable-pf-helper

  PrimMeta-Eq : Eq PrimMeta
  PrimMeta-Eq = Listable.Listable→Eq PrimMeta-Listable

  PrimMeta-EqB : EqB PrimMeta
  PrimMeta-EqB = Eq→EqB

  PrimMeta-Show : Show PrimMeta
  PrimMeta-Show .show Let           = "Let"
  PrimMeta-Show .show AnnLet        = "AnnLet"
  PrimMeta-Show .show SetEval       = "SetEval"
  PrimMeta-Show .show ShellCmd      = "ShellCmd"
  PrimMeta-Show .show CheckTerm     = "CheckTerm"
  PrimMeta-Show .show Parse         = "Parse"
  PrimMeta-Show .show Normalize     = "Normalize"
  PrimMeta-Show .show HeadNormalize = "HeadNormalize"
  PrimMeta-Show .show InferType     = "InferType"
  PrimMeta-Show .show Import        = "Import"
  PrimMeta-Show .show GetEval       = "GetEval"
  PrimMeta-Show .show Print         = "Print"
  PrimMeta-Show .show WriteFile     = "WriteFile"
  PrimMeta-Show .show CommandLine   = "CommandLine"
  PrimMeta-Show .show SetDebug      = "SetDebug"

primMetaArityF : PrimMeta → Fin 5
primMetaArityF Let           = 2F
primMetaArityF AnnLet        = 3F
primMetaArityF SetEval       = 3F
primMetaArityF ShellCmd      = 2F
primMetaArityF CheckTerm     = 2F
primMetaArityF Parse         = 3F
primMetaArityF Normalize     = 1F
primMetaArityF HeadNormalize = 1F
primMetaArityF InferType     = 1F
primMetaArityF Import        = 1F
primMetaArityF GetEval       = 0F
primMetaArityF Print         = 1F
primMetaArityF WriteFile     = 2F
primMetaArityF CommandLine   = 0F
primMetaArityF SetDebug      = 1F

primMetaArity : PrimMeta → ℕ
primMetaArity m = toℕ $ primMetaArityF m

primMetaArgs : Set → PrimMeta → Set
primMetaArgs A m = A Data.Vec.Recursive.^ (primMetaArity m)

mapPrimMetaArgs : (A → B) → primMetaArgs A m → primMetaArgs B m
mapPrimMetaArgs f = Data.Vec.Recursive.map f _

traversePrimMetaArgs : ⦃ Monad M ⦄ → (A → M B) → primMetaArgs A m → M (primMetaArgs B m)
traversePrimMetaArgs ⦃ mon ⦄ = Data.Vec.Recursive.Categorical.mapM mon

primMetaArgs-Show : (A → String) → primMetaArgs A m → String
primMetaArgs-Show showA = let showA' = λ s → "(" + showA s + ")"
  in Data.Vec.Recursive.foldr "" showA' (λ _ a s → showA' a <+> s) _

primMetaArgsZipWith : (A → B → C) → primMetaArgs A m → primMetaArgs B m → primMetaArgs C m
primMetaArgsZipWith f x y = Data.Vec.Recursive.zipWith f _ x y

primMetaArgsSequence : ⦃ Monad M ⦄ → primMetaArgs (M A) m → M (primMetaArgs A m)
primMetaArgsSequence ⦃ mon ⦄ = Data.Vec.Recursive.Categorical.sequenceM mon

primMetaArgsAnd : primMetaArgs Bool m → Bool
primMetaArgsAnd = Data.Vec.Recursive.foldr {P = const Bool} true id (const _∧_) _

primMetaArgsMax : primMetaArgs 𝕀 m → 𝕀
primMetaArgsMax = Data.Vec.Recursive.foldr {P = const 𝕀} 0 id (const _⊔𝕀_) _

primMetaArgsProd : primMetaArgs Set m → Set
primMetaArgsProd = Data.Vec.Recursive.foldr {P = const Set} ⊤ id (const _×_) _

module Types {T} (tl : TermLike T) where
  open TermLike tl
  private
    tString tTerm tStringList tProduct : T
    tString     = FreeVar "init$string"
    tStringList = FreeVar "init$stringList"
    tTerm       = FreeVar "init$term"
    tProduct    = FreeVar "init$product"
    tUnit       = FreeVar "init$unit"

  data Univ : Set where
    uStar uString uTerm uStringList : Univ
    uProduct : Univ → Univ → Univ

  ⟦_⟧ᵗ : Univ → T
  ⟦ uStar ⟧ᵗ = ⋆
  ⟦ uString ⟧ᵗ = tString
  ⟦ uTerm ⟧ᵗ = tTerm
  ⟦ uStringList ⟧ᵗ = tStringList
  ⟦ uProduct u u₁ ⟧ᵗ = tProduct ⟪$⟫ ⟦ u ⟧ᵗ ⟪$⟫ ⟦ u₁ ⟧ᵗ

  primMetaSᵘ : (m : PrimMeta) → primMetaArgs Univ m
  primMetaSᵘ Let           = (uString , uTerm)
  primMetaSᵘ AnnLet        = (uString , uTerm , uTerm)
  primMetaSᵘ SetEval       = (uTerm , uString , uString)
  primMetaSᵘ ShellCmd      = (uString , uStringList)
  primMetaSᵘ CheckTerm     = (uStar , uTerm)
  primMetaSᵘ Parse         = (uString , uStar , uString)
  primMetaSᵘ Normalize     = uTerm
  primMetaSᵘ HeadNormalize = uTerm
  primMetaSᵘ InferType     = uTerm
  primMetaSᵘ Import        = uString
  primMetaSᵘ GetEval       = _
  primMetaSᵘ Print         = uString
  primMetaSᵘ WriteFile     = (uString , uString)
  primMetaSᵘ CommandLine   = _
  primMetaSᵘ SetDebug      = uStringList

  primMetaS : (m : PrimMeta) → primMetaArgs T m
  primMetaS m = mapPrimMetaArgs ⟦_⟧ᵗ (primMetaSᵘ m)

  primMetaT : (m : PrimMeta) → primMetaArgs T m → T
  primMetaT Let _             = tUnit
  primMetaT AnnLet _          = tUnit
  primMetaT SetEval _         = tUnit
  primMetaT ShellCmd _        = tString
  primMetaT CheckTerm (t , _) = t
  primMetaT Parse (_ , t , _) = tProduct ⟪$⟫ t ⟪$⟫ tString
  primMetaT Normalize _       = tTerm
  primMetaT HeadNormalize _   = tTerm
  primMetaT InferType     _   = tTerm
  primMetaT Import _          = tUnit
  primMetaT GetEval _         = tTerm
  primMetaT Print   _         = tUnit
  primMetaT WriteFile _       = tUnit
  primMetaT CommandLine _     = tStringList
  primMetaT SetDebug _        = tUnit
