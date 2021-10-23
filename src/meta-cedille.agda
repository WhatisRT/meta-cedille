{-# OPTIONS --type-in-type #-}

module meta-cedille where

open import Data.String using (toList)
open import IO using (Main; run)
open import Monads.Except
open import Monads.ExceptT

open import Prelude
open import Prelude.Strings

open import Parse.Generate
open import Parse.TreeConvert
open import Bootstrap.InitEnv

open import CoreTheory
open import Execution

record EvalFlags : Set where
  field
    printAnything : Bool
    printInfo     : Bool -- print the results generated by a top level command

open EvalFlags

initFlagsDefault : EvalFlags
initFlagsDefault = record
  { printAnything = false
  ; printInfo     = false
  }

runtimeFlagsDefault : EvalFlags
runtimeFlagsDefault = record
  { printAnything = true
  ; printInfo     = true
  }

eval : MetaContext → String → EvalFlags → IO (MetaContext × Bool)
eval Γ input flags =
  if null (toList input)
    then return (Γ , true)
    else do
      (s , res) ← execute (tryExecute input) Γ
      -- let doesn't work in the next line?
      (Γ' , err , out) ← return $ case res of λ
        { (inj₁ x) → (Γ , x , "")
        ; (inj₂ (y , _)) → (contextFromState s , "" , concat (intersperse "\n" y)) }
      putStrErr err
      if printAnything flags
        then putStr (if printInfo flags then out else "")
        else return tt
      return (Γ' , null (toList err))

rep : MetaContext → IO MetaContext
rep Γ = do
  putStr "\nλ> "
  flushStdout
  input ← getLine
  proj₁ <$> eval Γ input runtimeFlagsDefault

{-# NON_TERMINATING #-}
loop : ∀ {a} {A : Set a} → A → (A → IO A) → IO ⊤
loop start f = do
  res ← f start
  loop res f

repl : MetaContext → IO ⊤
repl start = loop start rep

record Options : Set where
  field
    startRepl   : Bool
    importFiles : List String
    verbose     : Bool
    showHelp    : Bool

defaultOptions : Options
defaultOptions = record
  { startRepl   = true
  ; importFiles = []
  ; verbose     = false
  ; showHelp    = false }

{-# TERMINATING #-}
readOptions : ExceptT IO String Options
readOptions = do
  args ← getArgs
  return $ readArgs args defaultOptions
  where
    argumentDec : Decidable _
    argumentDec s = false ≟ isInit "--" (toList s)

    readArgs : List String → Options → Except String Options
    readArgs [] current = return current
    readArgs (x ∷ input) current =
      decCase x
        of
          ("--no-repl" , readArgs input record current { startRepl = false }) ∷
          ("--load"    , (case span argumentDec input of λ where
            (files , rest) → readArgs rest record current { importFiles = files })) ∷
          ("--verbose" , readArgs input record current { verbose = true }) ∷
          ("--help"    , readArgs input record current { showHelp = true }) ∷
          []
        default inj₁ ("Unknown option: " + x)

helpString : String
helpString = "Usage: meta-cedille [OPTIONS...]\n" +
  concat ((λ { (fst , snd) → "    --" + padRight ' ' padLength fst + snd + "\n" }) <$> helpTable)
  where
    helpTable : List (String × String)
    helpTable =
      ("help"         , "Show this help") ∷
      ("load [FILES]" , "Loads a list of files before starting the REPL") ∷
      ("verbose"      , "Print supressed output before starting the REPL") ∷
      ("no-repl"      , "Exits the program when the REPL would start") ∷ []

    padLength : ℕ
    padLength = 4 + maximum (Data.String.length ∘ proj₁ <$> helpTable)

open import Monads.Identity

initGrammar : Grammar
initGrammar = from-inj₂ (preCoreGrammar {ExceptT Id String}
  {{ExceptT-Monad {{Id-Monad}}}} {{ExceptT-MonadExcept {{Id-Monad}}}})

emptyMetaContext : MetaContext
emptyMetaContext = emptyGlobalContext , (initGrammar , "" , Sort-A □)

loadFiles : MetaContext → EvalFlags → List String → IO (MetaContext × Bool)
loadFiles context flags files =
  if null files
    then return (context , true)
    else eval context (concat $ map (λ file → "import " + file + ".") files) flags

main : Main
main = run $ do
  options ← readOptions
  case options of λ where
    (inj₁ x) → putStr x
    (inj₂ o) → let open Options o in
      if showHelp then putStr helpString else do
        (init , successInit) ← eval emptyMetaContext initEnv initFlagsDefault
        let initFlags = if verbose then runtimeFlagsDefault else initFlagsDefault
        (postLoad , successLoad) ← loadFiles init initFlags importFiles
        if startRepl
          then repl postLoad
          else if successInit ∧ successLoad
            then exitSuccess
            else exitFailure
