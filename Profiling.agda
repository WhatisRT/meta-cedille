--------------------------------------------------------------------------------
-- This file provides functions to deal with profiling information generated by
-- the profiler monad
--------------------------------------------------------------------------------

module Profiling where

import Agda.Builtin.Nat
open import Data.List hiding (concat; lookup)
open import Data.String using (toList; fromList; concat)
open import Data.String.Exts
open import Data.These hiding (alignWith; map)

open import Prelude

record ProfilingFlags : Set where
  field
    printDetailedProfiling : Bool -- show arguments that identify the step
    detailedPrintingCutoff : ℕ -- the number of characters printed when printing detailed info
    profilingTreeDepth : ℕ -- the maximum depth of the profiling tree
    profilingMinDuration : ℕ -- the minimum duration a step needs to have to be printed (in ms)

open ProfilingFlags

-- print picoseconds in a nice format
showPS : ℕ -> String
showPS n = case splitAt 6 $ drop 6 $ reverse $ toList $ show n of
  λ { (a , b) -> fromList $ reverse ((alignWith (λ
    { (this x) → x
    ; (that x) → x
    ; (these x x₁) → x}) a (replicate 6 '0')) ++ b) }

ms : ℕ
ms = 1000000000

{-# TERMINATING #-} -- the length of the second argument decreases in every recursive call
filterInfo : {A : Set} -> (A × ℕ -> Bool) -> List (A × ℕ) -> List (A × ℕ)
filterInfo P [] = []
filterInfo P (x ∷ []) = [ x ]
filterInfo P (x ∷ y ∷ l) = if P y
  then x ∷ (filterInfo P (y ∷ l))
  else filterInfo P (((proj₁ x) , (proj₂ x + proj₂ y)) ∷ l)

filterByLength : {A : Set} -> ℕ -> (List A) × ℕ -> Bool
filterByLength n (fst , snd) = ⌊ length fst <? n ⌋

filterByTime : {A : Set} -> ℕ -> (List A) × ℕ -> Bool
filterByTime n (fst , snd) = Agda.Builtin.Nat._<_ n snd

-- turn absolute times into relative times
accumulateInfo : {A : Set} -> List (A × ℕ) -> List (A × ℕ)
accumulateInfo [] = []
accumulateInfo (x ∷ []) = []
accumulateInfo ((_ , t') ∷ x@(n , t) ∷ l) = (n , t' ∸ t) ∷ accumulateInfo (x ∷ l)

-- we assume the list is sorted correctly already
showProfilingInfo : ProfilingFlags -> List (List (String × List String) × ℕ) -> String
showProfilingInfo flags = print ∘ (filterInfo profilingFilter) ∘ accumulateInfo
  where
    profilingFilter : ∀ {A} -> List A × ℕ -> Bool
    profilingFilter x = filterByLength (profilingTreeDepth flags) x
      ∧ filterByTime (profilingMinDuration flags * ms) x

    printProfilingIdentification : String × List String -> String
    printProfilingIdentification (fst , snd) = fst + (if printDetailedProfiling flags
      then "` (" + (concat $ intersperse ", " $
        map (shortenString (detailedPrintingCutoff flags)) snd) + ")"
      else "")

    print : List (List (String × List String) × ℕ) -> String
    print [] = ""
    print ((fst , snd) ∷ i) =
      print i + "\n" +
      (concat $ intersperse ";" $ reverse (map printProfilingIdentification fst)) +
      " " + showPS snd
