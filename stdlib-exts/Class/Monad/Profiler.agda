module Class.Monad.Profiler where

open import Class.Monad
open import Class.Monad.IO
open import Class.Monad.State
open import Data.List
open import Data.Maybe
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Unit
open import Function
open import IO.Exts
open import Level

record MonadProfiler {a b} (M : Set a -> Set b) {{_ : Monad M}} (W : Set a) : Set (suc a ⊔ b) where
  field
    logTime : (List W) -> M (Lift a ⊤)
    profileCall : ∀ {A} -> W -> M A -> M A

open MonadProfiler {{...}} public

module Profiling {a b} {M : Set a -> Set b} {W} {{_ : Monad M}} {{_ : MonadIO M}} {{st : MonadState M (List (List W × ℕ))}} where
  private
    logTime' : List W -> M (Lift a ⊤)
    logTime' w = do
      t <- liftIO $ liftIOLevel getCPUTime
      modify ((w , lower t) ∷_)

    profileCall' : ∀ {A} -> W -> M A -> M A
    profileCall' w x = do
      w' <- get {{_}} {{st}}
      let old = case head w' of λ { (just (w , t)) → w ; nothing → [] }
      logTime' (w ∷ old)
      res <- x
      logTime' old
      return res

  IOState-MonadProfiler : MonadProfiler M W
  IOState-MonadProfiler = record { logTime = logTime' ; profileCall = profileCall' }

open Profiling public
