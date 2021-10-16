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
  Normalize     : PrimMeta
  HeadNormalize : PrimMeta

private
  variable
    m : PrimMeta

instance
  PrimMeta-Eq : Eq PrimMeta
  PrimMeta-Eq = record { _≟_ = helper }
    where
      helper : (m m' : PrimMeta) → Dec (m ≡ m')
      helper EvalStmt EvalStmt = yes refl
      helper EvalStmt ShellCmd = no (λ ())
      helper EvalStmt CheckTerm = no (λ ())
      helper EvalStmt Normalize = no (λ ())
      helper EvalStmt HeadNormalize = no (λ ())
      helper ShellCmd EvalStmt = no (λ ())
      helper ShellCmd ShellCmd = yes refl
      helper ShellCmd CheckTerm = no (λ ())
      helper ShellCmd Normalize = no (λ ())
      helper ShellCmd HeadNormalize = no (λ ())
      helper CheckTerm EvalStmt = no (λ ())
      helper CheckTerm ShellCmd = no (λ ())
      helper CheckTerm CheckTerm = yes refl
      helper CheckTerm Normalize = no (λ ())
      helper CheckTerm HeadNormalize = no (λ ())
      helper Normalize EvalStmt = no (λ ())
      helper Normalize ShellCmd = no (λ ())
      helper Normalize CheckTerm = no (λ ())
      helper Normalize Normalize = yes refl
      helper Normalize HeadNormalize = no (λ ())
      helper HeadNormalize EvalStmt = no (λ ())
      helper HeadNormalize ShellCmd = no (λ ())
      helper HeadNormalize CheckTerm = no (λ ())
      helper HeadNormalize Normalize = no (λ ())
      helper HeadNormalize HeadNormalize = yes refl

  PrimMeta-EqB : EqB PrimMeta
  PrimMeta-EqB = Eq→EqB

  PrimMeta-Show : Show PrimMeta
  PrimMeta-Show = record { show = helper }
    where
      helper : PrimMeta → String
      helper EvalStmt      = "EvalStmt"
      helper ShellCmd      = "ShellCmd"
      helper CheckTerm     = "CheckTerm"
      helper Normalize     = "Normalize"
      helper HeadNormalize = "HeadNormalize"

primMetaArity : PrimMeta → ℕ
primMetaArity EvalStmt      = 1
primMetaArity ShellCmd      = 2
primMetaArity CheckTerm     = 2
primMetaArity Normalize     = 1
primMetaArity HeadNormalize = 1

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
