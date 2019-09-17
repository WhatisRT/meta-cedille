module IO.Exts where

import IO.Primitive as Prim
open import Class.Monad
open import Data.List
open import Data.Nat using (ℕ)
open import Data.String
open import Data.Sum
open import Data.Unit
open import Function
open import IO using (IO; run; readFiniteFile; lift)
open import IO.Instance
open import Level

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
  getLinePrim : Prim.IO String
  flushStdoutPrim : Prim.IO ⊤
  getCPUTimePrim : Prim.IO ℕ
  getArgsPrim : Prim.IO (List String)
  putStrErrPrim : String -> Prim.IO ⊤
  exitFailurePrim : ∀ {A : Set} -> Prim.IO A
  exitSuccessPrim : ∀ {A : Set} -> Prim.IO A
  runShellCmdPrim : String -> List String -> Prim.IO String
  catchIOErrorPrim : ∀ {A : Set} -> Prim.IO A -> (String -> Prim.IO A) -> Prim.IO A

{-# COMPILE GHC getLinePrim = fmap pack getLine #-}
{-# COMPILE GHC flushStdoutPrim = hFlush stdout #-}
{-# COMPILE GHC getCPUTimePrim = getCPUTime #-}
{-# COMPILE GHC getArgsPrim = fmap (fmap pack) getArgs #-}
{-# COMPILE GHC putStrErrPrim = hPutStr stderr . unpack #-}
{-# COMPILE GHC exitFailurePrim = \ _ -> exitFailure #-}
{-# COMPILE GHC exitSuccessPrim = \ _ -> exitSuccess #-}
{-# COMPILE GHC runShellCmdPrim = \ s t -> pack <$> (readProcess (unpack s) (fmap unpack t) "") #-} -- use haskell proc
{-# COMPILE GHC catchIOErrorPrim = \ _ a f -> catchIOError a (f . pack . show) #-}

getLine : IO String
getLine = lift getLinePrim

flushStdout : IO ⊤
flushStdout = lift flushStdoutPrim

getCPUTime : IO ℕ
getCPUTime = lift getCPUTimePrim

getArgs : IO (List String)
getArgs = lift getArgsPrim

liftIOLevel : ∀ {a b} {A : Set a} -> IO A -> IO (Lift b A)
liftIOLevel x = lift ((run x) Prim.>>= λ y -> Prim.return (lift y))

putStrErr : String -> IO ⊤
putStrErr s = lift (putStrErrPrim s)

exitFailure : ∀ {A} -> IO A
exitFailure = lift exitFailurePrim

exitSuccess : ∀ {A} -> IO A
exitSuccess = lift exitSuccessPrim

runShellCmd : String -> List String -> IO String
runShellCmd s args = lift (runShellCmdPrim s args)

catchIOError : ∀ {A : Set} -> IO A -> (String -> IO A) -> IO A
catchIOError a f = lift $ catchIOErrorPrim (run a) (run ∘ f)

readFiniteFileError : String -> IO (String ⊎ String)
readFiniteFileError name =
  catchIOError
    (do
      res <- readFiniteFile name
      return (inj₂ res)) (return ∘ inj₁)
