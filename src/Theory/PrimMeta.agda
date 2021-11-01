open import Class.Listable
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.Any
import Data.Vec.Recursive
import Data.Vec.Recursive.Categorical

open import Prelude

module Theory.PrimMeta where

private
  variable
    A B C : Set
    M : Set → Set

data PrimMeta : Set where
  EvalStmt      : PrimMeta
  ShellCmd      : PrimMeta
  CheckTerm     : PrimMeta
  Parse         : PrimMeta
  Normalize     : PrimMeta
  HeadNormalize : PrimMeta
  InferType     : PrimMeta

private
  variable
    m : PrimMeta

instance
  PrimMeta-Eq : Eq PrimMeta
  PrimMeta-Eq = Listable.Listable→Eq record
    { listing = EvalStmt ∷ ShellCmd ∷ CheckTerm ∷ Parse ∷ Normalize ∷ HeadNormalize ∷ InferType ∷ []
    ; unique = ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷
                 ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷
                 ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷
                 ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷
                 ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ [] ∷ []
    ; complete = λ where
        EvalStmt      → here refl
        ShellCmd      → there (here refl)
        CheckTerm     → there (there (here refl))
        Parse         → there (there (there (here refl)))
        Normalize     → there (there (there (there (here refl))))
        HeadNormalize → there (there (there (there (there (here refl)))))
        InferType     → there (there (there (there (there (there (here refl)))))) }

  PrimMeta-EqB : EqB PrimMeta
  PrimMeta-EqB = Eq→EqB

  PrimMeta-Show : Show PrimMeta
  PrimMeta-Show = record { show = helper }
    where
      helper : PrimMeta → String
      helper EvalStmt      = "EvalStmt"
      helper ShellCmd      = "ShellCmd"
      helper CheckTerm     = "CheckTerm"
      helper Parse         = "Parse"
      helper Normalize     = "Normalize"
      helper HeadNormalize = "HeadNormalize"
      helper InferType     = "InferType"

primMetaArity : PrimMeta → ℕ
primMetaArity EvalStmt      = 1
primMetaArity ShellCmd      = 2
primMetaArity CheckTerm     = 2
primMetaArity Parse         = 3
primMetaArity Normalize     = 1
primMetaArity HeadNormalize = 1
primMetaArity InferType     = 1

primMetaArgs : Set → PrimMeta → Set
primMetaArgs A m  = A Data.Vec.Recursive.^ (primMetaArity m)

mapPrimMetaArgs : (A → B) → primMetaArgs A m → primMetaArgs B m
mapPrimMetaArgs f = Data.Vec.Recursive.map f _

traversePrimMetaArgs : {{Monad M}} → (A → M B) → primMetaArgs A m → M (primMetaArgs B m)
traversePrimMetaArgs {{mon}} = Data.Vec.Recursive.Categorical.mapM mon

primMetaArgs-Show : (A → String) → primMetaArgs A m → String
primMetaArgs-Show showA = Data.Vec.Recursive.foldr "" showA (λ _ a s → showA a + s) _

primMetaArgsZipWith : (A → B → C) → primMetaArgs A m → primMetaArgs B m → primMetaArgs C m
primMetaArgsZipWith f x y = Data.Vec.Recursive.zipWith f _ x y

primMetaArgsSequence : {{Monad M}} → primMetaArgs (M A) m → M (primMetaArgs A m)
primMetaArgsSequence {{mon}} = Data.Vec.Recursive.Categorical.sequenceM mon

primMetaArgsAnd : primMetaArgs Bool m → Bool
primMetaArgsAnd = Data.Vec.Recursive.foldr {P = const Bool} true id (const _∧_) _
