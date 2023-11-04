module Theory.Evaluation where

open import Prelude
open import Class.Monad.Reader

open import Theory.Context
open import Theory.Terms

import Theory.Normalisation
import Theory.NBE

private variable
  a b : Bool

record EvalInfo : Set where
  field doLog : Bool
open EvalInfo

record Eval (T : Set) (M : Set → Set) ⦃ _ : Monad M ⦄ ⦃ _ : MonadReader M EvalInfo ⦄ : Set where
  field hnf normalize : Context → T → M T

module _ where
  instance
    _ = Monad-ReaderT
    _ = MonadReader-ReaderT

  module RunEval {T M} ⦃ _ : Monad M ⦄ (eval : Eval T (ReaderT EvalInfo M)) where

    open Eval eval

    runHnf : Bool → Context → T → M T
    runHnf b Γ t = hnf Γ t (record { doLog = b })

    runNf : Bool → Context → T → M T
    runNf b Γ t = normalize Γ t (record { doLog = b })

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ ⦃ _ : MonadReader M EvalInfo ⦄ where

  open Eval

  EvalNBE : Eval (PureTerm false) M
  EvalNBE .hnf       Γ t = do
    false ← reader doLog
      where true → return $ Theory.NBE.hnfLog Γ t
    return $ Theory.NBE.hnf Γ t
  -- no log here
  EvalNBE .normalize Γ t = return $ Theory.NBE.nf Γ t

  EvalNaive : Eval (Term a false) M
  EvalNaive .hnf       Γ t = reader doLog >>= λ l → return $ Theory.Normalisation.Norm.hnfNorm   l Γ t
  EvalNaive .normalize Γ t = reader doLog >>= λ l → return $ Theory.Normalisation.Norm.normalize l Γ t

  -- use the most efficient strategy
  EvalEfficient : Eval (Term a false) M
  EvalEfficient {a = false} = EvalNBE
  EvalEfficient {a = true}  = EvalNaive

module _ {a} {M : Set → Set} ⦃ _ : Monad M ⦄ where
  instance
    _ = Monad-ReaderT
    _ = MonadReader-ReaderT

  hnfNorm : Bool → Context → Term a false → M (Term a false)
  hnfNorm = RunEval.runHnf EvalEfficient

  normalize : Bool → Context → Term a false → M (Term a false)
  normalize = RunEval.runNf EvalEfficient
