--------------------------------------------------------------------------------
-- This file is the entry point for checking or executing code. It provides the
-- type MetaContext, which tracks the entire state of the interpreter as well as
-- the function tryExecute to parse and execute some code if possible
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Execution where

open import Prelude hiding (measureTime)

open import Class.Monad.Except
open import Class.Monad.IO
open import Class.Monad.State
open import Data.HSTrie

open import Conversion
open import Parse.Generate
open import Parse.TreeConvert
open import Theory.TypeChecking

open StringErr

record MetaEnv : Set where
  field
    grammar   : Grammar
    namespace : String  -- we need to remember the current namespace
                        -- because the rule string in the grammar doesn't
    grammarValid : Bool -- whether we need to update the grammar if we
                        -- don't change the namespace
    evaluator : AnnTerm
    evaluatorArgType : AnnTerm -- type of arguments to the evaluator
    doProfiling : Bool

-- The full state of the interpreter: the context of defined values plus parsing
-- and semantics for generating code
MetaContext : Set
MetaContext = GlobalContext × MetaEnv

getParserNamespace : Context → String → List String
getParserNamespace (Γ , _) n = strDrop (strLength n + 1) <$> (trieKeys $ lookupHSTrie n Γ)

module _ {M : Set → Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} {{_ : MonadIO M}} where

  getContext : M Context
  getContext = gets (globalToContext ∘ proj₁)

  getMeta : M MetaEnv
  getMeta = gets proj₂

  measureTime : ∀ {A} → String → M A → M A
  measureTime s x = do
    record { doProfiling = true } ← getMeta
      where _ → x
    Prelude.measureTime s x

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

  ⟦_⟧ˢ : Univ {true} {false} → Set
  ⟦ uStar ⟧ˢ = PureTerm
  ⟦ uString ⟧ˢ = String
  ⟦ uTerm ⟧ˢ = AnnTerm
  ⟦ uStringList ⟧ˢ = List String
  ⟦ uProduct u u₁ ⟧ˢ = ⟦ u ⟧ˢ × ⟦ u₁ ⟧ˢ

  primMetaSˢ : (m : PrimMeta) → Set
  primMetaSˢ m = primMetaArgsProd $ mapPrimMetaArgs ⟦_⟧ˢ (primMetaSᵘ {true} {false} m)

  showPrimMetaSˢ : {m : PrimMeta} → primMetaSˢ m → String
  showPrimMetaSˢ {Let} (t , t₁) = "Let (" + show t <+> "," <+> show t₁ + ")"
  showPrimMetaSˢ {AnnLet} (t , t₁ , t₂) =
    "AnnLet (" + show t <+> "," <+> show t₁ <+> "," <+> show t₂ + ")"
  showPrimMetaSˢ {SetEval} (t , t₁ , t₂) =
    "SetEval (" + show t <+> "," <+> show t₁ <+> "," <+> show t₂ + ")"
  showPrimMetaSˢ {ShellCmd} (t , t₁) = "ShellCmd (" + show t <+> "," <+> show t₁ + ")"
  showPrimMetaSˢ {CheckTerm} (t , t₁) = "CheckTerm (" + show t <+> "," <+> show t₁ + ")"
  showPrimMetaSˢ {Parse} (t , t₁ , t₂) =
    "Parse (" + show t <+> "," <+> show t₁ <+> "," <+> show t₂ + ")"
  showPrimMetaSˢ {Normalize} t = "Normalize (" + show t + ")"
  showPrimMetaSˢ {HeadNormalize} t = "HeadNormalize (" + show t + ")"
  showPrimMetaSˢ {InferType} t = "InferType (" + show t + ")"
  showPrimMetaSˢ {Import} t = "Import (" + show t + ")"
  showPrimMetaSˢ {GetEval} _ = "GetEval (" + "" + ")"
  showPrimMetaSˢ {Print} t = "Print (" + show t + ")"
  showPrimMetaSˢ {WriteFile} (t , t₁) = "WriteFile (" + show t <+> "," <+> show t₁ + ")"
  showPrimMetaSˢ {CommandLine} _ = "CommandLine (" + "" + ")"
  showPrimMetaSˢ {ToggleProf} _ = "ToggleProf (" + "" + ")"

  convertPrimArgs : (m : PrimMeta) → primMetaArgs PureTerm m → M (primMetaSˢ m)
  convertPrimArgs Let (t , t₁) = do
    t ← measureTime "Name" $ (M String ∋ unquoteFromTerm t)
    t₁ ← measureTime ("Def:" <+> show t₁) $ (M AnnTerm ∋ unquoteFromTerm t₁)
    return (t , t₁)
  convertPrimArgs AnnLet (t , t₁ , t₂) = do
    t ← (M String ∋ unquoteFromTerm t)
    t₁ ← (M AnnTerm ∋ unquoteFromTerm t₁)
    t₂ ← (M AnnTerm ∋ unquoteFromTerm t₂)
    return (t , t₁ , t₂)
  convertPrimArgs SetEval (t , t₁ , t₂) = do
    t ← (M AnnTerm ∋ unquoteFromTerm t)
    t₁ ← (M String ∋ unquoteFromTerm t₁)
    t₂ ← (M String ∋ unquoteFromTerm t₂)
    return (t , t₁ , t₂)
  convertPrimArgs ShellCmd (t , t₁) = do
    t ← (M String ∋ unquoteFromTerm t)
    t₁ ← (M (List String) ∋ unquoteFromTerm t₁)
    return (t , t₁)
  convertPrimArgs CheckTerm (t , t₁) = do
    t₁ ← (M AnnTerm ∋ unquoteFromTerm t₁)
    return (t , t₁)
  convertPrimArgs Parse (t , t₁ , t₂) = do
    t ← (M String ∋ unquoteFromTerm t)
    t₂ ← (M String ∋ unquoteFromTerm t₂)
    return (t , t₁ , t₂)
  convertPrimArgs Normalize t = do
    t ← (M AnnTerm ∋ unquoteFromTerm t)
    return t
  convertPrimArgs HeadNormalize t = do
    t ← (M AnnTerm ∋ unquoteFromTerm t)
    return t
  convertPrimArgs InferType t = do
    t ← (M AnnTerm ∋ unquoteFromTerm t)
    return t
  convertPrimArgs Import t = do
    t ← (M String ∋ unquoteFromTerm t)
    return t
  convertPrimArgs GetEval _ = return _
  convertPrimArgs Print t = do
    t ← (M String ∋ unquoteFromTerm t)
    return t
  convertPrimArgs WriteFile (t , t₁) = do
    t ← (M String ∋ unquoteFromTerm t)
    t₁ ← (M String ∋ unquoteFromTerm t₁)
    return (t , t₁)
  convertPrimArgs CommandLine _ = return _
  convertPrimArgs ToggleProf _ = return _

module ExecutionDefs {M : Set → Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} {{_ : MonadIO M}}
  where

  returnQuoted : ∀ {A} → ⦃ Quotable A ⦄ → A → M AnnTerm
  returnQuoted a = return (quoteToAnnTerm a)

  {-# NON_TERMINATING #-}
  -- Execute a term of type M t for some t
  executeTerm executeTerm' : PureTerm → M PureTerm
  executeBootstrapStmt : BootstrapStmt → M ⊤
  executePrimitive : (m : PrimMeta) → primMetaSˢ m → M AnnTerm
  -- Parse and execute a string
  parseAndExecute' parseAndExecuteBootstrap : String → M String
  parseAndExecute : String → M ⊤

  executeTerm t = do
    Γ ← getContext
    t ← measureTime "HNF" (return $ hnfNormPure Γ t)
    measureTime ("execHNF:" <+> show t) (executeTerm' t)

  executeTerm' (Mu t t₁) = do
    t' ← measureTime "Mu1" $ executeTerm t
    measureTime ("Mu2:" <+> show t') $ executeTerm (t₁ ⟪$⟫ t')

  executeTerm' (Epsilon t) = return t

  executeTerm' (Gamma t t') = catchError (executeTerm t) (λ s → executeTerm (t' ⟪$⟫ quoteToPureTerm s))

  executeTerm' (Ev m t) = do
    args ← measureTime "Converting arguments" $ convertPrimArgs m t
    t' ← measureTime ("Executing:" <+> showPrimMetaSˢ {m = m} args) $ executePrimitive m args
    measureTime "Sanity checking" $ appendIfError (checkTypePure t' $ primMetaT m t)
                  ("Bug: Result type mismatch in ζ" + show m)
    return (Erase t')

  {-# CATCHALL #-}
  executeTerm' t =
    throwError ("Error: " + shortenString 2000 (show t) + " is not a term that can be evaluated!")

  executePrimitive Let (n , t) = do
    returnQuoted =<< appendIfError (executeBootstrapStmt (Let n t nothing))
                                   ("Couldn't define" <+> n <+> ":=" <+> show t)

  executePrimitive AnnLet (n , t , T) = do
    returnQuoted =<< appendIfError (executeBootstrapStmt (Let n t (just T)))
                                   ("Couldn't define" <+> n <+> ":=" <+> show t <+> ":" <+> show T)

  executePrimitive SetEval (ev , NT , namespace) = do
    returnQuoted =<< executeBootstrapStmt (SetEval ev NT namespace)

  executePrimitive ShellCmd (cmd , args) = do
    returnQuoted =<< (liftIO $ runShellCmd cmd args)

  executePrimitive CheckTerm (t , u) = do
    Γ ← getContext
    T' ← inferType u
    appendIfError (checkβηPure Γ t $ Erase T')
      ("CheckTerm: Type mismatch with the provided type!\nProvided: " + show t +
        "\n\nSynthesized: " + show T')
    return u

  executePrimitive Parse (nonTerminal , type , text) = do
    Γ ← getContext
    record { grammar = G ; namespace = namespace } ← getMeta
    NT ← maybeToError (findNT G nonTerminal)
                      ("Non-terminal" <+> nonTerminal <+> "does not exist in the current grammar!")
    (res , parsed , rest) ← parse G NT namespace text
    T ← appendIfError (synthType Γ res)
                      ("\n\nError while interpreting input: "
                        + (shortenString 10000 (show res))
                        + "\nWhile parsing: " + (shortenString 10000 parsed))
    appendIfError (checkβηPure Γ type $ Erase T)
      ("Parse: Type mismatch with the provided type!\nProvided: " + show type +
        "\nSynthesized: " + show T)
    -- need to spell out instance manually, since we don't want to quote 'res'
    returnQuoted ⦃ Quotable-ProductData ⦃ Quotable-NoQuoteAnnTerm ⦄ ⦄
      record { lType = T ; rType = FreeVar "init$string" ; l = res ; r = rest }

  executePrimitive Normalize t = do
    Γ ← getContext
    returnQuoted (normalize Γ t)

  executePrimitive HeadNormalize t = do
    Γ ← getContext
    returnQuoted (hnfNorm Γ t)

  executePrimitive InferType t = do
    Γ ← getContext
    returnQuoted =<< synthType Γ t

  executePrimitive Import x = do
    res ← liftIO $ readFileError (x + ".mced")
    case res of λ where
      (inj₁ x) → throwError x
      (inj₂ y) → parseAndExecute y >> returnQuoted tt

  executePrimitive GetEval _ = do
    returnQuoted =<< MetaEnv.evaluator <$> getMeta

  executePrimitive Print s = do
    returnQuoted =<< (liftIO $ putStr s)

  executePrimitive WriteFile (fName , contents) = do
    returnQuoted =<< (liftIO $ writeFile fName contents)

  executePrimitive CommandLine _ = do
    returnQuoted =<< liftIO getArgs

  executePrimitive ToggleProf _ = do
    menv@record { doProfiling = b } ← getMeta
    returnQuoted =<< setMeta record menv { doProfiling = not b }

  executeBootstrapStmt (Let n t T) = do
    T ← case T of λ where
      (just T) → checkType t T >> return T
      nothing  → inferType t
    addDef n (record { def = just t ; type = T; extra = nothing })
    menv@record { namespace = namespace } ← getMeta
    if strTake (strLength namespace) n ≣ namespace
      then setMeta record menv { grammarValid = false } else return _

  executeBootstrapStmt (SetEval t n start) = do
    Γ ← getContext
    menv@record { grammar = G ; namespace = n' ; grammarValid = valid } ← getMeta
    y ← if n ≣ n' ∧ valid
      then return G
      else (generateCFG start $ getParserNamespace Γ n)
    (Pi _ u u₁) ← hnfNorm Γ <$> synthType Γ t
      where _ → throwError "The evaluator needs to have a pi type"
    true ← return $ isLocallyClosed (Erase u) Γ
      where false → throwError "The argument type to the evaluator cannot contain local variables!"
    case (hnfNorm Γ u₁) of λ where
      (M-T _) → do
        -- take the least normalized term that's locally free
        t' ∷ _ ← return $ boolFilter (λ t → isLocallyClosed (Erase t) Γ) (t ∷ hnfNorm Γ t ∷ [])
          where _ → throwError "The evaluator needs to normalize to a term without local variables!"
        setMeta record menv { grammar = y ; namespace = n ; grammarValid = true ; evaluator = t' ; evaluatorArgType = u }
      _       → throwError "The evaluator needs to return a M type"

  executeBootstrapStmt Empty = return _

  parseAndExecuteBootstrap s = do
    record { grammar = G } ← getMeta
    (bs , parsed , rest) ← parseBootstrap G s
    appendIfError (executeBootstrapStmt bs) ("\n\nError while executing term" <+> show bs)
    return rest

  parseAndExecute' s = do
    Γ ← getContext
    m@record { evaluator = ev ; evaluatorArgType = evT } ← getMeta
    (t , parsed , rest) ← parseMeta m s
    measureTime "TC" $
      appendIfError (checkType t evT)
                    ("\n\nError while interpreting input: " + (shortenString 10000 $ show t)
                                      + "\nWhile parsing: " + (shortenString 10000 s))
    measureTime ("Exec:" <+> parsed) $
      appendIfError (executeTerm (Erase (ev ⟪$⟫ t)))
                    ("\n\nError while executing input:" <+> parsed + "\n")
    return rest

  parseAndExecute s = do
    record { evaluator = evaluator } ← getMeta
    rest ← case evaluator of λ where
      (Sort-T □) → parseAndExecuteBootstrap s
      _          → parseAndExecute' s
    if strNull rest then return _ else parseAndExecute rest

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
