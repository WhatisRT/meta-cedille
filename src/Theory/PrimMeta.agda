open import Class.Listable
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.Any
import Data.Vec.Recursive
import Data.Vec.Recursive.Categorical

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

private
  variable
    m : PrimMeta

instance
  PrimMeta-Eq : Eq PrimMeta
  PrimMeta-Eq = Listable.Listable→Eq record
    { listing =
        Let ∷ AnnLet ∷ SetEval ∷ ShellCmd ∷ CheckTerm ∷ Parse ∷ Normalize ∷ HeadNormalize ∷ InferType ∷ Import ∷ GetEval ∷ Print ∷ []
    ; complete = λ where
        Let           → here refl
        AnnLet        → there (here refl)
        SetEval       → there (there (here refl))
        ShellCmd      → there (there (there (here refl)))
        CheckTerm     → there (there (there (there (here refl))))
        Parse         → there (there (there (there (there (here refl)))))
        Normalize     → there (there (there (there (there (there (here refl))))))
        HeadNormalize → there (there (there (there (there (there (there (here refl)))))))
        InferType     → there (there (there (there (there (there (there (there (here refl))))))))
        Import        → there (there (there (there (there (there (there (there (there (here refl)))))))))
        GetEval       → there (there (there (there (there (there (there (there (there (there (here refl))))))))))
        Print         → there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))
    }

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

primMetaArity : PrimMeta → ℕ
primMetaArity Let           = 2
primMetaArity AnnLet        = 3
primMetaArity SetEval       = 3
primMetaArity ShellCmd      = 2
primMetaArity CheckTerm     = 2
primMetaArity Parse         = 3
primMetaArity Normalize     = 1
primMetaArity HeadNormalize = 1
primMetaArity InferType     = 1
primMetaArity Import        = 1
primMetaArity GetEval       = 0
primMetaArity Print         = 1

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

module _ {T} ⦃ _ : TermLike T ⦄ where
  private
    tString tTerm tStringList tMetaResult tProduct : T
    tString     = FreeVar "init$string"
    tStringList = FreeVar "init$stringList"
    tTerm       = FreeVar "init$term"
    tMetaResult = FreeVar "init$metaResult"
    tProduct    = FreeVar "init$product"
    tUnit       = FreeVar "Unit"

  primMetaS : (m : PrimMeta) → primMetaArgs T m
  primMetaS Let               = (tString , tTerm)
  primMetaS AnnLet            = (tString , tTerm , tTerm)
  primMetaS SetEval           = (tTerm , tString , tString)
  primMetaS ShellCmd          = (tString , tStringList)
  primMetaS CheckTerm         = (⋆ , tTerm)
  primMetaS Parse             = (tString , ⋆ , tString)
  primMetaS Normalize         = tTerm
  primMetaS HeadNormalize     = tTerm
  primMetaS InferType         = tTerm
  primMetaS Import            = tString
  primMetaS GetEval           = _
  primMetaS Print             = tString

  primMetaT : (m : PrimMeta) → primMetaArgs T m → T
  primMetaT Let _             = tMetaResult
  primMetaT AnnLet _          = tMetaResult
  primMetaT SetEval _         = tMetaResult
  primMetaT ShellCmd _        = tString
  primMetaT CheckTerm (t , _) = t
  primMetaT Parse (_ , t , _) = tProduct ⟪$⟫ t ⟪$⟫ tString
  primMetaT Normalize _       = tTerm
  primMetaT HeadNormalize _   = tTerm
  primMetaT InferType     _   = tTerm
  primMetaT Import _          = tMetaResult
  primMetaT GetEval _         = tTerm
  primMetaT Print   _         = tUnit
