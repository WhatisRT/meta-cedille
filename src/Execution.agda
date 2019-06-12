--------------------------------------------------------------------------------
-- This file is the entry point for checking or executing code. It provides the
-- type MetaContext, which tracks the entire state of the interpreter as well as
-- the function tryExecute to parse and execute some code if possible
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Execution where

open import Class.Map
open import Class.Monad.Except
open import Class.Monad.IO
open import Class.Monad.Profiler
open import Class.Monad.State
open import Class.Traversable
open import Data.List using (map; length)
open import Data.SimpleMap
open import Data.String using (fromList; toList)
open import Data.String.Exts
open import Data.Tree
open import Data.Word32
open import IO using (IO; readFiniteFile)
open import IO.Exts
open import IO.Instance
open import Monads.Except

open import Conversion
open import CoreTheory
open import InitEnv
open import ParseTreeConvert
open import Parser
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
MetaContext = GlobalContext × Grammar × List Char × AnnTerm

-- Many statements just return a single string, in which case this function can
-- be used
strResult : String -> MetaResult
strResult s = [ s ] , []

module StateHelpers {M : Set -> Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} where

  getContext : M Context
  getContext = gets (λ m -> (proj₁ m , []))

  get' : M GlobalContext
  get' = gets (λ m -> proj₁ m)

  getMeta : M (Grammar × List Char × AnnTerm)
  getMeta = gets proj₂

  modify' : (MetaContext -> MetaContext) -> M ⊤
  modify' f = modify f >> return tt

  setMeta : Grammar -> List Char -> AnnTerm -> M ⊤
  setMeta G namespace interpreter =
    modify' λ { (fst , snd) -> (fst , G , namespace , interpreter) }

  setContext : GlobalContext -> M ⊤
  setContext Γ = modify' λ { (fst , snd) → (Γ , snd) }

  modifyContext : (GlobalContext -> GlobalContext) -> M ⊤
  modifyContext f = do
    Γ <- getContext
    setContext (f (contextToGlobal Γ))

  addDef : GlobalName -> Def -> M String
  addDef n d = do
    Γ <- getContext
    case lookup n (contextToGlobal Γ) of λ
      { (just x) → throwError
        ("The name " + show n + " is already defined!")
      ; nothing → do
        modifyContext (insert n d)
        return $ "Defined " + show n + show d }

open StateHelpers

checkInit : List Char -> List Char -> Bool
checkInit [] l' = true
checkInit (x ∷ l) [] = false
checkInit (x ∷ l) (x₁ ∷ l') = x ≣ x₁ ∧ checkInit l l'

getParserNamespace : GlobalContext -> List Char -> List (List Char)
getParserNamespace Γ n = map (drop $ suc $ length n) $
  boolFilter (λ c -> checkInit n c) $
    map (toList ∘ (λ { (Global n) -> n }) ∘ proj₁) Γ

-- Folds a tree of constructors back into a term by properly applying the
-- constructors and prefixing the namespace
{-# TERMINATING #-}
parseResultToConstrTree : List Char -> Tree (List Char) -> AnnTerm
parseResultToConstrTree namespace (Node x x₁) = foldl
  (λ t t' -> App-A t t')
  (Var-A (Free (fromList (namespace ++ "$" ++ ruleToConstr x))))
  (map (parseResultToConstrTree namespace) x₁)

module ExecutionDefs {M : Set -> Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}}
  {{_ : MonadIO M}} {{_ : MonadProfiler M (String × List String)}}
  where

  -- Typecheck a term and return its type
  check : AnnTerm -> M AnnTerm
  check t = do
    Γ <- getContext
    synthType Γ t

  -- Parse the next top-level non-terminal symbol from a string, and return a
  -- term representing the result of the parse, as well as the unparsed rest of
  -- the string
  parseMeta : Grammar × List Char × AnnTerm -> String -> M (AnnTerm × String)
  parseMeta (G , namespace , interpreter) s = do
    (t , rest) <- parse' G s
    return (parseResultToConstrTree namespace t , rest)

  {-# NON_TERMINATING #-}
  -- Execute a term of type M t for some t
  executeTerm : AnnTerm -> M MetaResult
  executeStmt : Stmt -> M MetaResult
  -- Parse and execute a string in the pre-meta language
  tryExecute' : String -> M MetaResult
  -- Parse and execute a string
  tryExecute : String -> M MetaResult

  executeStmt (Let n t nothing) = do
    t' <- profileCall ("Typecheck" , [ show t ]) $ check t
    res <- addDef n (Let t t')
    return $ strResult res

  executeStmt (Let n t (just t')) = do
    u <- profileCall ("Typecheck" , [ show t ]) $ check t
    profileCall ("Typecheck" , [ show t' ]) $ check t'
    Γ <- getContext
    catchError (profileCall ("Equality" , show u ∷ show t' ∷ []) $ checkβη Γ u t')
      (λ e -> throwError $
        "Type mismatch with the provided type!\n" + e + "\nProvided: " + show t' +
        "\nSynthesized: " + show u + " which normalize to: " +
        show (normalize Γ t') + "\nand: " + show (normalize Γ u))
    res <- addDef n (Let t t')
    return $ strResult res

  executeStmt (Ass n t) = do
    t' <- check t
    res <- addDef n (Axiom t)
    return $ strResult res

  executeStmt (Normalize t) = do
    Γ <- getContext
    T <- synthType Γ t
    return $ strResult
      (show t + " : " + show T + " normalizes to: " +
      (show $ normalizePure Γ $ Erase t))

  executeStmt (HeadNormalize t) = do
    Γ <- getContext
    T <- synthType Γ t
    return $ strResult
      (show t + " : " + show T + " head-normalizes to: " +
      (show $ hnfNorm Γ t))

  executeStmt (EraseSt t) = return $ strResult $ show $ Erase t

  executeStmt (Test t) = do
    Γ <- getContext
    return $ strResult $ show $ normalizePure Γ $ Erase t

  executeStmt (SetEval t n start) = do
    Γ <- get'
    let Γ' = globalToContext Γ
    let rules = getParserNamespace Γ (toList n)
    maybe
      (λ rules' -> do
        y <- generateCFG (toList start) rules'
        T <- synthType Γ' t
        case (hnfNorm Γ' T) of λ
          { (Π u u₁) -> do
            appendIfError (checkβη Γ' u (Var-A (Free (n + "$" + start))))
              "The evaluator needs to accept the parse result as input"
            case (hnfNorm Γ' u₁) of λ
              { (M-A _) -> do
                setMeta y (toList n) t
                return (strResult "Successfully set the evaluator")
              ; _ -> throwError "The evaluator needs to return a M type" }
          ; _ -> throwError "The evaluator needs to have a pi type" }
      )
      (throwError "Error while un-escaping parsing rules!")
      (sequence $ map translate rules)

  executeStmt (Import x) = do
    res <- profileCall ("IO" , [ x + ".mced" ]) $ liftIO $ readFiniteFileError (x + ".mced")
    case res of λ
      { (inj₁ x) → throwError x
      ; (inj₂ y) → tryExecute y }

  executeStmt (Shell t) = do
    Γ <- getContext
    T <- synthType Γ t
    appendIfError (checkβη Γ T (Var-A $ Free $ "init$string"))
      "The term passed to a shell statement needs to be of type string"
    s <- constrsToString Γ $ normalizePure Γ $ Erase t
    res <- liftIO $ runShellCmd s
    return $ strResult res

  executeStmt Empty = return (strResult "")

  executeTerm (μ t t₁) = do
    Γ <- getContext
    t' <- executeTerm (hnfNorm Γ t)
    executeTerm (App-A t₁ $ embedMetaResult t')

  executeTerm (ε t) = return ([] , [ t ])

  executeTerm (Ev-A t) = do
    Γ <- getContext
    stmt <- appendIfError (constrsToStmt Γ $ normalizePure Γ $ Erase t) ("Error with term: " + (show $ Erase t))
    executeStmt stmt
  {-# CATCHALL #-}
  executeTerm t =
    throwError ("Error: " + show t + " is not a term that can be evaluated!")

  tryExecute' s = do
    (fst , snd) <- profileCall ("Parse" , [ s ]) (parseStmt s)
    res <- appendIfError (profileCall ("Execute" , [ show fst ]) $ executeStmt fst)
                         ("\n\nError while executing statement: " + show fst)
    res' <- if strNull snd then return ([] , []) else tryExecute' snd
    return (res + res')

  tryExecute s = do
    Γ <- getContext
    m@(_ , _ , interpreter) <- getMeta
    case interpreter of λ
      { (Sort-A □') -> tryExecute' s -- this is the default interpreter that gets used to start the language
      ; _ -> do
        (fst , snd) <- profileCall ("ParseMeta" , [ s ]) $ parseMeta m s
        let exec = App-A interpreter fst
        T <- profileCall ("TypecheckEval" , [ show exec ]) $ synthType Γ exec
        case (hnfNorm Γ T) of λ
          { (M-A _) -> do
            res <- profileCall ("Execute" , [ show exec ]) $
              appendIfError
                (executeTerm (hnfNorm Γ exec))
                ("\n\nError while executing input: " + s + "\nThe corresponding term is: " + show exec)
            res' <- if strNull snd then return mzero else tryExecute snd
            return (res + res')
          ; _ -> throwError "Trying to execute something that isn't of type M t. This should never happen!" }
      }

module ExecutionMonad where
  open import Monads.ExceptT
  open import Monads.StateT
  open import Monads.WriterT
  open import Class.Monad.Profiler

  -- profiling in the second component
  ExecutionState : Set
  ExecutionState = MetaContext × List (List (String × List String) × ℕ)

  contextFromState : ExecutionState -> MetaContext
  contextFromState = proj₁

  profilingFromState : ExecutionState -> List (List (String × List String) × ℕ)
  profilingFromState = proj₂

  Execution : Set -> Set
  Execution = ExceptT (StateT (WriterT IO Log) ExecutionState) String

  execute : ∀ {A} -> Execution A -> MetaContext -> IO (Log × ExecutionState × (String ⊎ A))
  execute x Γ = do
    ((x' , s') , log) <- x (Γ , [])
    return (log , s' , x')

  instance
    Execution-Monad : Monad Execution
    Execution-Monad = ExceptT-Monad {{StateT-Monad {{WriterT-Monad}}}}

    Execution-MonadExcept : MonadExcept Execution {{Execution-Monad}} String
    Execution-MonadExcept = ExceptT-MonadExcept {{StateT-Monad {{WriterT-Monad}}}}

    Execution-MonadState : MonadState Execution {{Execution-Monad}} ExecutionState
    Execution-MonadState =
      ExceptT-MonadState {{StateT-Monad {{WriterT-Monad}}}} {{StateT-MonadState {{WriterT-Monad}}}}

    Execution-MonadState-MetaContext : MonadState Execution {{Execution-Monad}} MetaContext
    Execution-MonadState-MetaContext = MonadStateProj₁ {{Execution-Monad}} {{Execution-MonadState}}

    Execution-MonadState-Profiling :
      MonadState Execution {{Execution-Monad}} (List (List (String × List String) × ℕ))
    Execution-MonadState-Profiling = MonadStateProj₂ {{Execution-Monad}} {{Execution-MonadState}}

    Execution-IO : MonadIO Execution {{Execution-Monad}}
    Execution-IO = ExceptT-MonadIO
      {{StateT-Monad {{WriterT-Monad}}}}
      {{StateT-MonadIO {{WriterT-Monad}} {{WriterT-MonadIO {{_}} {{_}} {{IO-MonadIO}}}}}}

    Execution-Profiler : MonadProfiler Execution {{Execution-Monad}} (String × List String)
    Execution-Profiler = IOState-MonadProfiler {{Execution-Monad}}

open ExecutionMonad public
open ExecutionDefs {Execution} public
