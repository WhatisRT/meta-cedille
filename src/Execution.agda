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

import Theory.Terms
open import Conversion
open import Parse.Generate
open import Parse.TreeConvert
open import Theory.NBE
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
    doDebug : List String

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

  logTypeEnabled : String → M Bool
  logTypeEnabled type = do
    record { doDebug = doDebug } ← getMeta
    return $ not $ null (filter (_≟ type) doDebug)

  logWithType : ∀ {A} → String → String → M A → M A
  logWithType type s x = do
    b ← logTypeEnabled type
    if b then Prelude.measureTime s x else x

  logProfile : ∀ {A} → String → M A → M A
  logProfile = logWithType "profile"

  logProfileBasic : ∀ {A} → String → M A → M A
  logProfileBasic = logWithType "profileBasic"

  modify' : (MetaContext → MetaContext) → M ⊤
  modify' f = modify f >> return tt

  setMeta : MetaEnv → M ⊤
  setMeta menv = modify' λ { (Γ , _) → (Γ , menv) }

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
    t ← normalize false Γ t
    catchError (liftExcept $ unquoteConstrs Γ t)
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
  showPrimMetaSˢ {SetDebug} _ = "SetDebug (" + "" + ")"
  showPrimMetaSˢ {GetDef} t = "GetDef (" + show t + ")"

  convertPrimArgs : (m : PrimMeta) → primMetaArgs PureTerm m → M (primMetaSˢ m)
  convertPrimArgs Let (t , t₁) = do
    t ← logProfile "Name" $ (M String ∋ unquoteFromTerm t)
    t₁ ← logProfile ("Def:" <+> show t₁) $ (M AnnTerm ∋ unquoteFromTerm t₁)
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
  convertPrimArgs SetDebug t = do
    t ← (M (List String) ∋ unquoteFromTerm t)
    return t
  convertPrimArgs GetDef t = do
    t ← (M String ∋ unquoteFromTerm t)
    return t

module ExecutionDefs {M : Set → Set} {{_ : Monad M}}
  {{_ : MonadExcept M String}} {{_ : MonadState M MetaContext}} {{_ : MonadIO M}}
  where

  returnQuoted : ∀ {A} → ⦃ Quotable A ⦄ → A → M AnnTerm
  returnQuoted a = return (quoteToAnnTerm a)

  {-# NON_TERMINATING #-}
  -- Execute a term of type M t for some t
  executeTerm executeTerm' : Theory.Terms.PureTerm true → M (Theory.Terms.PureTerm true)
  executeBootstrapStmt : BootstrapStmt → M ⊤
  executePrimitive : (m : PrimMeta) → primMetaSˢ m → M AnnTerm
  -- Parse and execute a string
  parseAndExecute' parseAndExecuteBootstrap : String → M String
  parseAndExecute : String → M ⊤

  executeTerm t = do
    b ← logTypeEnabled "evalMeta"
    Γ ← C.convContext false <$> getContext
    t ← logProfile "HNF" (return $ hnfExec b Γ t)
    logProfile ("execHNF:" <+> show t) (executeTerm' t)

  executeTerm' (Mu t t₁) = do
    t' ← logProfile ("Mu1:" <+> show t) $ executeTerm t
    logProfile ("Mu2:" <+> show (t₁ ⟪$⟫ t')) $ executeTerm (t₁ ⟪$⟫ t')

  executeTerm' (Epsilon t) = return t

  executeTerm' (App2 (Const-N CatchM 0) t t') =
    catchError (executeTerm t) (λ s → executeTerm (t' ⟪$⟫ toNBETerm (quoteToPureTerm s)))

  executeTerm' u@(Ev m t) = do
    Γ ← C.convContext false <$> getContext
    let x = mapPrimMetaArgs (toPureTerm false (length (proj₂ Γ)) Γ) t
    args ← logProfile "Converting arguments" $ convertPrimArgs m x
    t' ← logProfile ("Executing:" <+> showPrimMetaSˢ {m = m} args) $ executePrimitive m args
    logProfile "Sanity checking" $ appendIfError (checkTypePure t' $ primMetaT m x)
                  ("Bug: Result type mismatch in" <+> showPrimMetaSˢ {m = m} args + "\n"
                  + show t' <+> "doesn't have type" <+> show (primMetaT m t))
    return (Erase (toNBETerm t'))

  {-# CATCHALL #-}
  executeTerm' t =
    throwError ("Error: " + shortenString 2000 (show t) + " is not a term that can be evaluated!")

  executePrimitive Let (n , t) = do
    returnQuoted =<< appendIfError (executeBootstrapStmt (Let n t nothing))
                                   ("\n\nCouldn't define" <+> n <+> ":=" <+> show t)

  executePrimitive AnnLet (n , t , T) = do
    returnQuoted =<< appendIfError (executeBootstrapStmt (Let n t (just T)))
                                   ("\n\nCouldn't define" <+> n <+> ":=" <+> show t <+> ":" <+> show T)

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
    b ← logTypeEnabled "normalize"
    e ← logTypeEnabled "erase"
    mif b ∧ e then normalize b Γ (Erase t) >>= liftIO ∘ putStrLn ∘ show
    normalize (b ∧ not e) Γ t >>= returnQuoted

  executePrimitive HeadNormalize t = do
    Γ ← getContext
    b ← logTypeEnabled "headNormalize"
    e ← logTypeEnabled "erase"
    mif b ∧ e then hnfNorm b Γ (Erase t) >>= liftIO ∘ putStrLn ∘ show
    hnfNorm (b ∧ not e) Γ t >>= returnQuoted

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
    returnQuoted =<< liftIO (putStr s >> flushStdout >> return tt)

  executePrimitive WriteFile (fName , contents) = do
    returnQuoted =<< liftIO (writeFile fName contents)

  executePrimitive CommandLine _ = do
    returnQuoted =<< liftIO getArgs

  executePrimitive SetDebug opts = do
    menv ← getMeta
    returnQuoted =<< setMeta record menv { doDebug = opts }

  executePrimitive GetDef n = do
    Γ ← getContext
    case (lookupInContext (Free n) Γ) of λ where
      nothing → throwError (n <+> "is not a defined name!")
      (just record { def = nothing }) → throwError (n <+> "is a postulate!")
      (just record { def = (just t) }) → returnQuoted t

  executeBootstrapStmt (Let n t T) = do
    T ← case T of λ where
      (just T) → checkType t T >> return T
      nothing  → inferType t
    addDef n (record { def = just t ; type = T ; extra = nothing })
    menv@record { namespace = namespace } ← getMeta
    mif strTake (strLength namespace) n ≣ namespace
      then setMeta record menv { grammarValid = false }

  executeBootstrapStmt (SetEval t n start) = do
    Γ ← getContext
    menv@record { grammar = G ; namespace = n' ; grammarValid = valid } ← getMeta
    y ← if n ≣ n' ∧ valid
      then return G
      else (generateCFG start $ getParserNamespace Γ n)
    (Pi Regular _ u u₁) ← hnfNorm false Γ =<< synthType Γ t
      where _ → throwError "The evaluator needs to have a pi type"
    true ← return $ isLocallyClosed u Γ
      where false → throwError "The argument type to the evaluator cannot contain local variables!"
    (M-T _) ← hnfNorm false Γ u₁
      where _ → throwError "The evaluator needs to return a M type"
    -- take the least normalized term that's locally free
    x ← hnfNorm false Γ t
    t' ∷ _ ← return $ boolFilter (λ t → isLocallyClosed t Γ) (t ∷ x ∷ [])
      where _ → throwError "The evaluator needs to normalize to a term without local variables!"
    setMeta record menv { grammar = y ; namespace = n ; grammarValid = true ; evaluator = t' ; evaluatorArgType = u }

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
    logProfileBasic ("Type checking parse result:" <+> parsed) $
      appendIfError (checkType t evT)
                    ("\n\nError while interpreting input: " + (shortenString 10000 $ show t)
                                      + "\nWhile parsing: " + (shortenString 10000 s))
    logProfileBasic ("Execute parse result:" <+> parsed) $
      appendIfError (executeTerm (Erase $ toNBETerm (ev ⟪$⟫ t)))
                    ("\n\nError while executing input:" <+> parsed + "\n")
    return rest

  parseAndExecute s = do
    record { evaluator = evaluator } ← getMeta
    rest ← case evaluator of λ where
      □ → parseAndExecuteBootstrap s
      _ → parseAndExecute' s
    mif not (strNull rest) then parseAndExecute rest

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
