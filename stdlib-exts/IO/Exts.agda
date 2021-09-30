{-# OPTIONS --type-in-type --guardedness #-}

module IO.Exts where

import IO.Primitive as Prim
open import Class.Monad
open import Class.Functor
open import Data.List
open import Data.Nat using (ℕ)
open import Data.String
open import Data.Sum
open import Data.Unit
open import Function
open import IO using (IO; run; readFiniteFile; lift)
open import IO.Instance
open import Level

private
  variable
    A : Set

{-#
  FOREIGN GHC
  import Data.Text
  import System.CPUTime
  import System.Environment
  import System.Exit
  import System.IO
  import System.IO.Error
  import System.Process
#-}

postulate
  flushStdoutPrim : Prim.IO ⊤
  getCPUTimePrim : Prim.IO ℕ
  putStrErrPrim : String → Prim.IO ⊤
  runShellCmdPrim : String → List String → Prim.IO String
  catchIOErrorPrim : Prim.IO A → (String → Prim.IO A) → Prim.IO A

{-# COMPILE GHC flushStdoutPrim = hFlush stdout #-}
{-# COMPILE GHC getCPUTimePrim = getCPUTime #-}
{-# COMPILE GHC putStrErrPrim = hPutStr stderr . unpack #-}
{-# COMPILE GHC runShellCmdPrim = \ s t -> pack <$> (readProcess (unpack s) (fmap unpack t) "") #-} -- use haskell proc
{-# COMPILE GHC catchIOErrorPrim = \ _ a f -> catchIOError a (f . pack . show) #-}

flushStdout : IO ⊤
flushStdout = lift flushStdoutPrim

getCPUTime : IO ℕ
getCPUTime = lift getCPUTimePrim

putStrErr : String → IO ⊤
putStrErr s = lift (putStrErrPrim s)

runShellCmd : String → List String → IO String
runShellCmd s args = lift (runShellCmdPrim s args)

catchIOError : IO A → (String → IO A) → IO A
catchIOError a f = lift $ catchIOErrorPrim (run a) (run ∘ f)

readFiniteFileError : String → IO (String ⊎ String)
readFiniteFileError name =
  catchIOError (inj₂ <$> readFiniteFile name) (return ∘ inj₁)
