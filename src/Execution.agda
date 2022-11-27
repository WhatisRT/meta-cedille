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
open import Theory.TypeChecking

open import Parse.TreeConvert using (parseBootstrap; parse; BootstrapStmt; Let; SetEval; Empty)
open import Parse.Generate

open import Prelude
open import Prelude.Strings
open import Prelude.Nat

open StringErr

record MetaEnv : Set where
  field
    grammar   : Grammar
    namespace : String  -- we need to remember the current namespace
                        -- because the rule string in the grammar doesn't
    evaluator : AnnTerm
    evaluatorArgType : AnnTerm -- type of arguments to the evaluator

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

  unquoteFromTerm : ∀ {A} ⦃ _ : Unquote A ⦄ → PureTerm → M A
  unquoteFromTerm t = do
    Γ ← getContext
    catchError (unquoteConstrs Γ $ normalizePure Γ t)
               (λ e → throwError $ "Error while unquoting" <+> show t + ":\n" + e)

  -- Typecheck a term and return its type
  inferType : AnnTerm → M AnnTerm
  inferType t = do
    Γ ← getContext
    synthType Γ t

  checkType : AnnTerm → AnnTerm → M ⊤
  checkType t T = do
    t' ← inferType t
    inferType T
    Γ ← getContext
    catchError (checkβη Γ T t')
      (λ e → throwError $
        "checkType: Type mismatch with the provided type!\n" + e + "\nProvided:    " + show T +
        "\nSynthesized:" <+> show t')

  checkTypePure : AnnTerm → PureTerm → M ⊤
  checkTypePure t T = do
    t' ← inferType t
    Γ ← getContext
    catchError (checkβηPure Γ T $ Erase t')
      (λ e → throwError $
        "checkTypePure: Type mismatch with the provided type!\n" + e + "\nProvided:    " + show T +
        "\nSynthesized:" <+> show t')

  parseMeta : MetaEnv → String → M (AnnTerm × String × String)
  parseMeta menv s = let open MetaEnv menv in parse grammar (initNT grammar) namespace s

module ExecutionDefs {M : Set → Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} {{_ : MonadIO M}}
  where

  {-# NON_TERMINATING #-}
  -- Execute a term of type M t for some t
  executeTerm executeTerm' : PureTerm → M (MetaResult × PureTerm)
  executeBootstrapStmt : BootstrapStmt → M (MetaResult × AnnTerm)
  executePrimitive : (m : PrimMeta) → primMetaArgs PureTerm m → M (MetaResult × AnnTerm)
  -- Parse and execute a string
  parseAndExecute' parseAndExecuteBootstrap : String → M (MetaResult × String)
  parseAndExecute : String → M MetaResult

  executeTerm t = do
    Γ ← getContext
    executeTerm' (hnfNormPure Γ t)

  executeTerm' (Mu t t₁) = do
    (res , t') ← executeTerm t
    (res' , resTerm) ← executeTerm (t₁ ⟪$⟫ t')
    return (res + res' , resTerm)

  executeTerm' (Epsilon t) = return (([] , []) , t)

  executeTerm' (Gamma t t') = catchError (executeTerm t) (λ s → executeTerm (t' ⟪$⟫ quoteToPureTerm s))

  executeTerm' (Ev m t) = do
    (res , t') ← executePrimitive m t
    appendIfError (checkTypePure t' $ primMetaT m t)
                  ("Bug: Result type mismatch in ζ" + show m)
    return (res , Erase t')

  {-# CATCHALL #-}
  executeTerm' t =
    throwError ("Error: " + shortenString 2000 (show t) + " is not a term that can be evaluated!")

  executePrimitive Let (n , t) = do
    n ← unquoteFromTerm n
    t ← unquoteFromTerm t
    appendIfError (executeBootstrapStmt (Let n t nothing))
                  ("Couldn't define" <+> n <+> ":=" <+> show t)

  executePrimitive AnnLet (n , t , T) = do
    n ← unquoteFromTerm n
    t ← unquoteFromTerm t
    T ← unquoteFromTerm T
    appendIfError (executeBootstrapStmt (Let n t (just T)))
                  ("Couldn't define" <+> n <+> ":=" <+> show t <+> ":" <+> show T)

  executePrimitive SetEval (ev , NT , namespace) = do
    t ← unquoteFromTerm ev
    n ← unquoteFromTerm NT
    start ← unquoteFromTerm namespace
    executeBootstrapStmt (SetEval t n start)

  executePrimitive ShellCmd (t , t') = do
    cmd ← unquoteFromTerm t
    args ← unquoteFromTerm t'
    res ← liftIO $ runShellCmd cmd args
    return (strResult res , quoteToAnnTerm res)

  executePrimitive CheckTerm (t , t') = do
    Γ ← getContext
    u ← unquoteFromTerm t'
    T' ← inferType u
    catchError (checkβηPure Γ t $ Erase T')
      (λ e → throwError $
        "Type mismatch with the provided type!\nProvided: " + show t +
        "\nSynthesized: " + show T')
    return (strResult "" , u)

  executePrimitive Parse (t , type , t') = do
    Γ ← getContext
    nonTerminal ← M String ∋ (unquoteFromTerm t)
    text ← M String ∋ (unquoteFromTerm t')
    record { grammar = G ; namespace = namespace } ← getMeta
    NT ← maybeToError (findNT G nonTerminal)
                      ("Non-terminal" <+> nonTerminal <+> "does not exist in the current grammar!")
    (res , parsed , rest) ← parse G NT namespace text
    T ← appendIfError (synthType Γ res)
                      ("\n\nError while interpreting input: "
                        + (shortenString 10000 (show res))
                        + "\nWhile parsing: " + (shortenString 10000 parsed))
    appendIfError (checkβηPure Γ type $ Erase T)
      ("Type mismatch with the provided type!\nProvided: " + show type +
        "\nSynthesized: " + show T)
    -- need to spell out instance manually, since we don't want to quote 'res'
    return (strResult "" , quoteToAnnTerm ⦃ Quotable-ProductData ⦃ Quotable-NoQuoteAnnTerm ⦄ ⦄
      record { lType = T ; rType = FreeVar "init$string" ; l = res ; r = rest })

  executePrimitive Normalize t = do
    Γ ← getContext
    u ← unquoteFromTerm t
    T ← synthType Γ u
    return (strResult
      (show u + " : " + show T + " normalizes to: " +
      (show $ normalize Γ u)) , quoteToAnnTerm (normalize Γ u))

  executePrimitive HeadNormalize t = do
    Γ ← getContext
    u ← unquoteFromTerm t
    T ← synthType Γ u
    return (strResult
      (show t + " : " + show T + " head-normalizes to: " +
      (show $ hnfNorm Γ u)) , (quoteToAnnTerm $ hnfNorm Γ u))

  executePrimitive InferType t = do
    Γ ← getContext
    u ← unquoteFromTerm t
    T ← synthType Γ u
    return (strResult "" , (quoteToAnnTerm T))

  executePrimitive Import t = do
    x ← M String ∋ (unquoteFromTerm t)
    res ← liftIO $ readFileError (x + ".mced")
    case res of λ where
      (inj₁ x) → throwError x
      (inj₂ y) → parseAndExecute y >>= λ res → return (res , quoteToAnnTerm tt)

  executePrimitive GetEval t = do
    ev ← MetaEnv.evaluator <$> getMeta
    return (strResult "" , quoteToAnnTerm ev)

  executePrimitive Print t = do
    s ← unquoteFromTerm t
    liftIO $ putStr s
    return (strResult "" , quoteToAnnTerm tt)

  executePrimitive WriteFile (t , t') = do
    fName ← unquoteFromTerm t
    contents ← unquoteFromTerm t'
    liftIO $ writeFile fName contents
    return (strResult "" , quoteToAnnTerm tt)

  executePrimitive CommandLine _ = do
    args ← liftIO getArgs
    return (strResult "" , quoteToAnnTerm args)

  executeBootstrapStmt (Let n t T) = do
    T ← case T of λ where
      (just T) → checkType t T >> return T
      nothing  → inferType t
    res ← addDef n (record { def = just t ; type = T; extra = nothing })
    return (strResult res , quoteToAnnTerm tt)

  executeBootstrapStmt (SetEval t n start) = do
    Γ ← getContext
    y ← generateCFG start $ getParserNamespace Γ n
    (Pi _ u u₁) ← hnfNorm Γ <$> synthType Γ t
      where _ → throwError "The evaluator needs to have a pi type"
    true ← return $ isLocallyClosed (Erase u) Γ
      where false → throwError "The argument type to the evaluator cannot contain local variables!"
    case (hnfNorm Γ u₁) of λ where
      (M-T _) → do
        -- take the least normalized term that's locally free
        t' ∷ _ ← return $ boolFilter (λ t → isLocallyClosed (Erase t) Γ) (t ∷ hnfNorm Γ t ∷ [])
          where _ → throwError "The evaluator needs to normalize to a term without local variables!"
        setMeta record { grammar = y ; namespace = n ; evaluator = t' ; evaluatorArgType = u }
        return (strResult "Successfully set the evaluator" , quoteToAnnTerm tt)
      _       → throwError "The evaluator needs to return a M type"

  executeBootstrapStmt Empty = return (strResult "" , quoteToAnnTerm tt)

  parseAndExecuteBootstrap s = do
    record { grammar = G } ← getMeta
    (fst , parsed , snd) ← parseBootstrap G s
    res ← appendIfError (proj₁ <$> executeBootstrapStmt fst) ("\n\nError while executing term" <+> show fst)
    return (res , snd)

  parseAndExecute' s = do
    Γ ← getContext
    m@record { evaluator = ev ; evaluatorArgType = evT } ← getMeta
    (fst , parsed , snd) ← parseMeta m s
    appendIfError (checkType fst evT) ("\n\nError while interpreting input: " + (shortenString 10000 (show fst))
                                        + "\nWhile parsing: " + (shortenString 10000 s))
    (res , _) ← appendIfError (executeTerm (Erase (ev ⟪$⟫ fst))) ("\n\nError while executing input:" <+> parsed + "\n")
    return (res , snd)

  parseAndExecute s = do
    record { evaluator = evaluator } ← getMeta
    (res , rest) ← case evaluator of λ where
      (Sort-T □) → parseAndExecuteBootstrap s
      _          → parseAndExecute' s
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
