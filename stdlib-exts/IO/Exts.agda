{-# OPTIONS --type-in-type --guardedness #-}

module IO.Exts where

import IO.Primitive as Prim
open import Class.Functor
open import Class.Monad
open import Class.Monad.IO
open import Data.Bool
open import Data.List hiding (_++_)
open import Data.Nat using (ℕ; _∸_; _<ᵇ_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Show
open import Data.String hiding (show)
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
  import Data.Text.Encoding.Error (lenientDecode)
  import Data.Text.Encoding (decodeUtf8With)
  import qualified Data.ByteString as BS
#-}

postulate
  flushStdoutPrim : Prim.IO ⊤
  getCPUTimePrim : Prim.IO ℕ
  putStrErrPrim : String → Prim.IO ⊤
  runShellCmdPrim : String → List String → Prim.IO String
  catchIOErrorPrim : Prim.IO A → (String → Prim.IO A) → Prim.IO A
  readFileUtf8Prim : String → Prim.IO String

{-# COMPILE GHC flushStdoutPrim = hFlush stdout #-}
{-# COMPILE GHC getCPUTimePrim = getCPUTime #-}
{-# COMPILE GHC putStrErrPrim = hPutStr stderr . unpack #-}
{-# COMPILE GHC runShellCmdPrim = \ s t -> pack <$> (readProcess (unpack s) (fmap unpack t) "") #-} -- use haskell proc
{-# COMPILE GHC catchIOErrorPrim = \ _ a f -> catchIOError a (f . pack . show) #-}
{-# COMPILE GHC readFileUtf8Prim = fmap (decodeUtf8With lenientDecode) . BS.readFile . unpack #-}

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

readFileUtf8 : String → IO String
readFileUtf8 = lift ∘ readFileUtf8Prim

readFileError : String → IO (String ⊎ String)
readFileError name =
  catchIOError (inj₂ <$> readFileUtf8 name) (return ∘ inj₁)

module _ {a} {M : Set a -> Set a} {{_ : Monad M}} {{_ : MonadIO M}} where

  printTimeStamp : M ⊤
  printTimeStamp = do
    t ← liftIO $ getCPUTime
    let milliseconds = t / 1000000000
    liftIO $ IO.putStr ("@" ++ show milliseconds ++ "ms: ")
    return _

  measureTime : String → M A → M A
  measureTime s x = do
    t ← liftIO $ getCPUTime
    a ← x
    t' ← liftIO $ getCPUTime
    let milliseconds = (t' ∸ t) / 1000000000
    if (1 <ᵇ milliseconds)
      then (printTimeStamp >> (liftIO $ IO.putStrLn (show milliseconds ++ "ms:" <+> s ++ "\n")))
      else return _
    return a
