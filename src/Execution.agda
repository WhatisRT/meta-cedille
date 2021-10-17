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
open import Data.String using (fromList; toList)
open import Data.Tree
open import IO using (IO; readFiniteFile)

open import Conversion
open import CoreTheory
open import Escape
open import ParseTreeConvert
open import ParserGenerator

open import Prelude
open import Prelude.Strings

Log : Set
Log = ⊤

instance
  Log-Monoid : Monoid Log
  Log-Monoid = Unit-Monoid

-- The full state of the interpreter: the context of defined values plus parsing
-- and semantics for generating code
MetaContext : Set
MetaContext = GlobalContext × Grammar × String × AnnTerm

-- Many statements just return a single string, in which case this function can
-- be used
strResult : String → MetaResult
strResult s = [ s ] , []

module StateHelpers {M : Set → Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} where

  getContext : M Context
  getContext = gets (λ m → (proj₁ m , []))

  get' : M GlobalContext
  get' = gets (λ m → proj₁ m)

  getMeta : M (Grammar × String × AnnTerm)
  getMeta = gets proj₂

  modify' : (MetaContext → MetaContext) → M ⊤
  modify' f = modify f >> return tt

  setMeta : Grammar → String → AnnTerm → M ⊤
  setMeta G namespace interpreter =
    modify' λ { (fst , snd) → (fst , G , namespace , interpreter) }

  setContext : GlobalContext → M ⊤
  setContext Γ = modify' λ { (fst , snd) → (Γ , snd) }

  modifyContext : (GlobalContext → GlobalContext) → M ⊤
  modifyContext f = do
    Γ ← getContext
    setContext (f (contextToGlobal Γ))

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

open StateHelpers

checkInit : List Char → List Char → Bool
checkInit [] l' = true
checkInit (x ∷ l) [] = false
checkInit (x ∷ l) (x₁ ∷ l') = x ≣ x₁ ∧ checkInit l l'

getParserNamespace : GlobalContext → String → List String
getParserNamespace Γ n = strDrop (strLength n + 1) <$> (trieKeys $ lookupHSTrie n Γ)

ruleToConstr : String → String
ruleToConstr = fromList ∘ concat ∘ helper ∘ groupEscaped ∘ toList
  where
    helper : List (List Char) → List (List Char)
    helper [] = []
    helper (l ∷ l₁) = (case l of λ where
      (c ∷ []) → if c ≣ '$' ∨ c ≣ '_' ∨ c ≣ '!' ∨ c ≣ '@' ∨ c ≣ '&'
        then [ c ]
        else escapeChar c
      (_ ∷ c ∷ []) → if l ≣ "\\$" ∨ l ≣ "\\_" ∨ l ≣ "\\!" ∨ l ≣ "\\@" ∨ l ≣ "\\&"
        then escapeChar c
        else l
      _ → l) ∷ (helper l₁)

-- Folds a tree of constructors back into a term by properly applying the
-- constructors and prefixing the namespace
{-# TERMINATING #-}
parseResultToConstrTree : String → Tree (String ⊎ Char) → AnnTerm
parseResultToConstrTree namespace (Node x x₁) =
  foldl (λ t t' → t ⟪$⟫ t') (ruleToTerm x) (parseResultToConstrTree namespace <$> x₁)
    where
      ruleToTerm : String ⊎ Char → AnnTerm
      ruleToTerm (inj₁ x) = FreeVar (namespace + "$" + ruleToConstr x)
      ruleToTerm (inj₂ y) = Char-A y

module ExecutionDefs {M : Set → Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} {{_ : MonadIO M}}
  where

  -- Typecheck a term and return its type
  check : AnnTerm → M AnnTerm
  check t = do
    Γ ← getContext
    synthType Γ t

  -- Parse the next top-level non-terminal symbol from a string, and return a
  -- term representing the result of the parse, as well as the unparsed rest of
  -- the string
  parseInit : (G : Grammar) → NonTerminal G → String → String → M (AnnTerm × String)
  parseInit G S namespace s = do
    (t , rest) ← parse'Init G S s
    return (parseResultToConstrTree namespace t , rest)

  parseMeta : Grammar × String × AnnTerm → String → M (AnnTerm × String)
  parseMeta (G , namespace , _) s = parseInit G (initNT G) namespace s

  {-# NON_TERMINATING #-}
  -- Execute a term of type M t for some t
  executeTerm : PureTerm → M (MetaResult × PureTerm)
  executeStmt : Stmt → M MetaResult
  -- Parse and execute a string in the pre-meta language
  tryExecute' : String → M MetaResult
  -- Parse and execute a string
  tryExecute : String → M MetaResult

  executeStmt (Let n t nothing) = do
    t' ← check t
    res ← addDef n (Let t t')
    return $ strResult res

  executeStmt (Let n t (just t')) = do
    u ← check t
    check t'
    Γ ← getContext
    catchError (checkβη Γ u t')
      (λ e → throwError $
        "Type mismatch with the provided type!\n" + e + "\nProvided: " + show t' +
        "\nSynthesized: " + show u)
    res ← addDef n (Let t t')
    return $ strResult res

  executeStmt (Ass n t) = do
    t' ← check t
    res ← addDef n (Axiom t)
    return $ strResult res

  executeStmt (SetEval t n start) = do
    Γ ← get'
    let Γ' = globalToContext Γ
    let rules = getParserNamespace Γ n
    maybe
      (λ rules' → do
        y ← generateCFG start rules'
        T ← synthType Γ' t
        case (hnfNorm Γ' T) of λ where
          (Pi-A _ u u₁) → do
            appendIfError (checkβη Γ' u $ FreeVar (n + "$" + start))
              "The evaluator needs to accept the parse result as input"
            case (hnfNorm Γ' u₁) of λ where
              (M-A _) → do
                setMeta y n t
                return (strResult "Successfully set the evaluator")
              _ → throwError "The evaluator needs to return a M type"
          _ → throwError "The evaluator needs to have a pi type")
      (throwError "Error while un-escaping parsing rules!")
      (sequence $ map ((_<$>_ fromList) ∘ translate ∘ toList) rules)

  executeStmt (Import x) = do
    res ← liftIO $ readFiniteFileError (x + ".mced")
    case res of λ where
      (inj₁ x) → throwError x
      (inj₂ y) → tryExecute y

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
    normStmt ← return $ normalizePure Γ t
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
    (G , namespace , _) ← getMeta
    NT ← maybeToError (findNT G nonTerminal) ("Non-terminal " + nonTerminal + " does not exist in the current grammar!")
    (res , rest) ← parseInit G NT namespace text
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

  tryExecute' s = do
    (fst , snd) ← parseStmt s
    res ← appendIfError (executeStmt fst) ("\n\nError while executing statement: " + show fst)
    res' ← if strNull snd then return ([] , []) else tryExecute' snd
    return (res + res')

  tryExecute s = do
    Γ ← getContext
    m@(_ , _ , interpreter) ← getMeta
    case interpreter of λ
      { (Sort-A □') → tryExecute' s -- this is the default interpreter that gets used to start the language
      ; _ → do
        (fst , snd) ← parseMeta m s
        let exec = interpreter ⟪$⟫ fst
        T ← appendIfError (synthType Γ exec)
                           ("\n\nError while interpreting input: "
                             + (shortenString 10000 (show fst))
                             + "\nWhile parsing: " + (shortenString 10000 s))
        case (hnfNorm Γ T) of λ
          { (M-A _) → do
            execHnf ← return $ hnfNormPure Γ $ Erase exec
            (res , _) ← appendIfError (executeTerm execHnf) ("\n\nError while executing input: " + s)
            res' ← if strNull snd then return mzero else tryExecute snd
            return (res + res')
          ; _ → throwError "Trying to execute something that isn't of type M t. This should never happen!" }
      }

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
