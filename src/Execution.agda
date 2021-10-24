--------------------------------------------------------------------------------
-- This file is the entry point for checking or executing code. It provides the
-- type MetaContext, which tracks the entire state of the interpreter as well as
-- the function tryExecute to parse and execute some code if possible
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Execution where

open import Class.Monad.Except
open import Class.Monad.IO
open import Class.Monad.State
open import Data.HSTrie

open import Conversion
open import CoreTheory

open import Parse.TreeConvert
open import Parse.Generate

open import Prelude
open import Prelude.Strings

record MetaEnv : Set where
  field
    grammar   : Grammar
    namespace : String  -- we need to remember the current namespace
                        -- because the rule string in the grammar doesn't
    evaluator : AnnTerm

-- The full state of the interpreter: the context of defined values plus parsing
-- and semantics for generating code
MetaContext : Set
MetaContext = GlobalContext × MetaEnv

-- Many statements just return a single string, in which case this function can
-- be used
strResult : String → MetaResult
strResult s = [ s ] , []

getParserNamespace : Context → String → List String
getParserNamespace (Γ , _) n = strDrop (strLength n + 1) <$> (trieKeys $ lookupHSTrie n Γ)

module _ {M : Set → Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} where

  getContext : M Context
  getContext = gets (globalToContext ∘ proj₁)

  getMeta : M MetaEnv
  getMeta = gets proj₂

  modify' : (MetaContext → MetaContext) → M ⊤
  modify' f = modify f >> return tt

  setMeta : MetaEnv → M ⊤
  setMeta menv =
    modify' λ { (Γ , _) → (Γ , menv) }

  setContext : GlobalContext → M ⊤
  setContext Γ = modify' λ { (_ , m) → (Γ , m) }

  modifyContext : (GlobalContext → GlobalContext) → M ⊤
  modifyContext f = do
    Γ ← getContext
    setContext $ f $ contextToGlobal Γ

  addDef : GlobalName → Def → M String
  addDef n d = do
    Γ ← getContext
    case insertInGlobalContext n d (contextToGlobal Γ) of λ where
      (inj₁ x) → throwError x
      (inj₂ y) → setContext y >> return ("Defined " + n + show d)

  termFromTerm : PureTerm → M AnnTerm
  termFromTerm t = do
    Γ ← getContext
    catchError (constrsToTerm Γ $ normalizePure Γ t)
               (λ e → throwError $ "Error while converting " + show t + " to a term")

  -- Typecheck a term and return its type
  check : AnnTerm → M AnnTerm
  check t = do
    Γ ← getContext
    synthType Γ t

  parseMeta : MetaEnv → String → M (AnnTerm × String)
  parseMeta menv s = let open MetaEnv menv in parse grammar (initNT grammar) namespace s

module ExecutionDefs {M : Set → Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} {{_ : MonadIO M}}
  where

  {-# NON_TERMINATING #-}
  -- Execute a term of type M t for some t
  executeTerm : PureTerm → M (MetaResult × PureTerm)
  executeStmt : Stmt → M MetaResult
  -- Parse and execute a string
  parseAndExecute' parseAndExecuteBootstrap : String → M (MetaResult × String)
  parseAndExecute : String → M MetaResult

  executeStmt (Let n t nothing) = do
    T ← check t
    strResult <$> addDef n (Let t T)

  executeStmt (Let n t (just t')) = do
    T ← check t
    check t'
    Γ ← getContext
    catchError (checkβη Γ T t')
      (λ e → throwError $
        "Type mismatch with the provided type!\n" + e + "\nProvided: " + show t' +
        "\nSynthesized: " + show T)
    strResult <$> addDef n (Let t t')

  executeStmt (Ass n t) = do
    _ ← check t
    strResult <$> addDef n (Axiom t)

  executeStmt (SetEval t n start) = do
    Γ ← getContext
    y ← generateCFG start $ getParserNamespace Γ n
    (Pi-A _ u u₁) ← hnfNorm Γ <$> synthType Γ t
      where _ → throwError "The evaluator needs to have a pi type"
    appendIfError (checkβη Γ u $ FreeVar (n + "$" + start))
      "The evaluator needs to accept the parse result as input"
    case (hnfNorm Γ u₁) of λ where
      (M-A _) → do
        setMeta record { grammar = y ; namespace = n ; evaluator = t }
        return $ strResult "Successfully set the evaluator"
      _       → throwError "The evaluator needs to return a M type"

  executeStmt (Import x) = do
    res ← liftIO $ readFiniteFileError (x + ".mced")
    case res of λ where
      (inj₁ x) → throwError x
      (inj₂ y) → parseAndExecute y

  executeStmt Empty = return (strResult "")

  executeTerm (Mu-P t t₁) = do
    Γ ← getContext
    (res , t') ← executeTerm (hnfNormPure Γ t)
    (res' , resTerm) ← executeTerm (hnfNormPure Γ (t₁ ⟪$⟫ t'))
    return (res + res' , resTerm)

  executeTerm (Epsilon-P t) = return (([] , []) , t)

  executeTerm (Gamma-P t t') =
    catchError (executeTerm t) (λ s → executeTerm (t' ⟪$⟫ Erase (stringToTerm s)))

  executeTerm (Ev-P EvalStmt t) = do
    Γ ← getContext
    let normStmt = normalizePure Γ t
    stmt ← appendIfError (constrsToStmt Γ normStmt) ("Error with term: " + show t)
    res ← executeStmt stmt
    return (res , Erase (embedMetaResult res))

  executeTerm (Ev-P ShellCmd (t , t')) = do
    Γ ← getContext
    cmd ← constrsToString Γ $ normalizePure Γ t
    args ← constrsToStringList Γ $ normalizePure Γ t'
    res ← liftIO $ runShellCmd cmd args
    return (strResult res , Erase (stringToTerm res))

  executeTerm (Ev-P CheckTerm (t , t')) = do
    Γ ← getContext
    u ← termFromTerm t'
    T' ← check u
    catchError (checkβηPure Γ t $ Erase T')
      (λ e → throwError $
        "Type mismatch with the provided type!\nProvided: " + show t +
        "\nSynthesized: " + show T')
    return (strResult "" , Erase u)

  -- TODO: return rest as well
  executeTerm (Ev-P Parse (t , type , t')) = do
    Γ ← getContext
    nonTerminal ← constrsToString Γ $ normalizePure Γ t
    text ← constrsToString Γ $ normalizePure Γ t'
    record { grammar = G ; namespace = namespace } ← getMeta
    NT ← maybeToError (findNT G nonTerminal) ("Non-terminal " + nonTerminal + " does not exist in the current grammar!")
    (res , rest) ← parse G NT namespace text
    T ← appendIfError (synthType Γ res)
                      ("\n\nError while interpreting input: "
                        + (shortenString 10000 (show res))
                        + "\nWhile parsing: " + (shortenString 10000 text))
    appendIfError (checkβηPure Γ type $ Erase T)
      ("Type mismatch with the provided type!\nProvided: " + show type +
        "\nSynthesized: " + show T)
    return (strResult "" , Erase res)

  executeTerm (Ev-P Normalize t) = do
    Γ ← getContext
    u ← termFromTerm t
    T ← synthType Γ u
    return (strResult
      (show u + " : " + show T + " normalizes to: " +
      (show $ normalizePure Γ $ Erase u)) , (Erase $ pureTermToTerm $ normalizePure Γ $ Erase u))

  executeTerm (Ev-P HeadNormalize t) = do
    Γ ← getContext
    u ← termFromTerm t
    T ← synthType Γ u
    return (strResult
      (show t + " : " + show T + " head-normalizes to: " +
      (show $ hnfNorm Γ u)) , (Erase $ termToTerm $ hnfNorm Γ u))

  -- executeStmt (EraseSt t) = return $ strResult $ show $ Erase t

  {-# CATCHALL #-}
  executeTerm t =
    throwError ("Error: " + show t + " is not a term that can be evaluated!")

  parseAndExecuteBootstrap s = do
    (fst , snd) ← parseStmt s
    res ← appendIfError (executeStmt fst) ("\n\nError while executing statement: " + show fst)
    return (res , snd)

  parseAndExecute' s = do
    Γ ← getContext
    m ← getMeta
    (fst , snd) ← parseMeta m s
    let exec = MetaEnv.evaluator m ⟪$⟫ fst
    (M-A _) ← hnfNorm Γ <$>
      appendIfError (synthType Γ exec)
                    ("\n\nError while interpreting input: "
                      + (shortenString 10000 (show fst))
                      + "\nWhile parsing: " + (shortenString 10000 s))
      where _ → throwError "Trying to execute something that isn't of type M t. This should never happen!"
    let execHnf = hnfNormPure Γ $ Erase exec
    (res , _) ← appendIfError (executeTerm execHnf) ("\n\nError while executing input: " + s)
    return (res , snd)

  parseAndExecute s = do
    record { evaluator = interpreter } ← getMeta
    (res , rest) ← case interpreter of λ where
      (Sort-A □') → parseAndExecuteBootstrap s
      _           → parseAndExecute' s
    res' ← if strNull rest then return mzero else parseAndExecute rest
    return (res + res')

module ExecutionMonad where
  open import Monads.ExceptT
  open import Monads.StateT

  ExecutionState : Set
  ExecutionState = MetaContext

  contextFromState : ExecutionState → MetaContext
  contextFromState s = s

  Execution : Set → Set
  Execution = ExceptT (StateT IO ExecutionState) String

  execute : ∀ {A} → Execution A → MetaContext → IO (ExecutionState × (String ⊎ A))
  execute x Γ = do
    (x' , s') ← x Γ
    return (s' , x')

  instance
    Execution-Monad : Monad Execution
    Execution-Monad = ExceptT-Monad {{StateT-Monad}}

    Execution-MonadExcept : MonadExcept Execution {{Execution-Monad}} String
    Execution-MonadExcept = ExceptT-MonadExcept {{StateT-Monad}}

    Execution-MonadState : MonadState Execution {{Execution-Monad}} ExecutionState
    Execution-MonadState = ExceptT-MonadState {{StateT-Monad}} {{StateT-MonadState}}

    Execution-IO : MonadIO Execution {{Execution-Monad}}
    Execution-IO = ExceptT-MonadIO {{StateT-Monad}} {{StateT-MonadIO {{_}} {{IO-MonadIO}}}}

open ExecutionMonad public
open ExecutionDefs {Execution} public
