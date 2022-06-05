--------------------------------------------------------------------------------
-- This file contains functions to turn the tree of parse results into the agda
-- data structures they represent.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Parse.TreeConvert where

import Data.Sum
open import Class.Map
open import Class.Monad.Except
open import Data.SimpleMap
open import Data.Map.String
open import Data.String using (fromList; toList; fromChar; uncons)
open import Data.Tree
open import Data.Tree.Instance
open import Data.Word using (fromℕ)

open import Prelude
open import Prelude.Strings

open import Theory.TypeChecking
open import Bootstrap.InitEnv
open import Parse.MultiChar
open import Parse.LL1
open import Parse.Generate
open import Parse.Escape

PTree : Set
PTree = Tree (ℕ ⊎ Char)

RuleType : Set
RuleType = Fin 5

ruleFun : Set → RuleType → Set
ruleFun A 0F = Maybe A
ruleFun A 1F = PTree → Maybe A
ruleFun A 2F = PTree → PTree → Maybe A
ruleFun A 3F = PTree → PTree → PTree → Maybe A
ruleFun A 4F = PTree → PTree → PTree → PTree → Maybe A

ruleIdMap : StringMap (StringMap ℕ)
ruleIdMap = mapSnd (fromListSM ∘ mapWithIndex (flip _,_)) $ fromListSM parseRuleMap

ruleId : String → String → Maybe (ℕ ⊎ Char)
ruleId nonterm rule = inj₁ <$> (lookup rule =<< lookup nonterm ruleIdMap)

_≡ᴹ_ : ℕ ⊎ Char → Maybe (ℕ ⊎ Char) → Bool
x ≡ᴹ y = just x ≣ y

ruleIdN : ∀ {A} → (n : RuleType) → String → String → ruleFun A n → List PTree → Maybe (ℕ ⊎ Char) × Maybe A
ruleIdN 0F s s' f [] = (ruleId s s' , f)
ruleIdN 1F s s' f (x₁ ∷ []) = (ruleId s s' , f x₁)
ruleIdN 2F s s' f (x₁ ∷ x₂ ∷ []) = (ruleId s s' , f x₁ x₂)
ruleIdN 3F s s' f (x₁ ∷ x₂ ∷ x₃ ∷ []) = (ruleId s s' , f x₁ x₂ x₃)
ruleIdN 4F s s' f (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) = (ruleId s s' , f x₁ x₂ x₃ x₄)
ruleIdN n s s' f _ = (ruleId s s' , nothing)

ruleCaseN : {A : Set} → PTree → String → List (List Char × Σ[ t ∈ RuleType ] ruleFun A t) → Maybe A
ruleCaseN (Node x x₁) r cs =
  decCase just x of map (λ where (x , t , f) → ruleIdN t r (fromList x) f x₁) cs default nothing

toSort : PTree → Maybe AnnTerm
toSort x = ruleCaseN x "sort" (("*" , 0F , just ⋆) ∷ ("□" , 0F , just □) ∷ [])

toConst : PTree → Maybe Const
toConst x = ruleCaseN x "const" (("Char" , 0F , just CharT) ∷ [])

toChar : PTree → Maybe Char
toChar (Node (inj₁ x) x₁) = nothing
toChar (Node (inj₂ y) x₁) = just y

toChar' : PTree → Maybe Char
toChar' x = ruleCaseN x "char" (("!!" , 1F , toChar) ∷ [])

toName : PTree → Maybe String
toName (Node x (y ∷ y' ∷ [])) = (λ y → fromChar y +_) <$₂> toChar y , toName y'
toName (Node x []) = if x ≡ᴹ ruleId "string'" "" then return "" else nothing
toName _ = nothing

toNameList : PTree → Maybe (List String)
toNameList (Node x []) = just []
toNameList (Node x (x₁ ∷ x₂ ∷ _)) = _∷_ <$₂> toName x₁ , toNameList x₂
toNameList _ = nothing

toIndex : PTree → Maybe ℕ
toIndex t = helper t >>= foldl {A = Maybe ℕ} (λ x c → (λ x' → 10 * x' + c) <$> x) (just 0)
  where
    helper'' : String → ℕ ⊎ Char → List ℕ → Maybe (List ℕ)
    helper'' r x rest =
      decCase (just x) of
        applyUpTo (λ n → ruleId r (show n + "_index'_") , return (n ∷ rest)) 10
        default nothing

    helper' : PTree → Maybe (List ℕ)
    helper' (Node x []) =
      if x ≡ᴹ ruleId "index'" ""
        then return []
        else nothing
    helper' (Node x (x₁ ∷ _)) = helper' x₁ >>= helper'' "index'" x

    helper : PTree → Maybe (List ℕ)
    helper (Node x []) = nothing
    helper (Node x (x₁ ∷ _)) = helper' x₁ >>= helper'' "index" x

{-# TERMINATING #-} -- inlining the termRuleN's would make the checker happy
toTerm : PTree → Maybe AnnTerm
toTerm = helper []
  where
    helper : List String → PTree → Maybe AnnTerm
    helper accu y =
      let conv1ʰ : (AnnTerm → AnnTerm) → ruleFun AnnTerm 1F
          conv1ʰ f x = f <$> helper accu x

          conv2ʰ : (AnnTerm → AnnTerm → AnnTerm) → ruleFun AnnTerm 2F
          conv2ʰ f x y = f <$₂> helper accu x , helper accu y

          conv3ʰ : (AnnTerm → AnnTerm → AnnTerm → AnnTerm) → ruleFun AnnTerm 3F
          conv3ʰ f x y z = do x ← helper accu x; y ← helper accu y; z ← helper accu z; return $ f x y z

          conv2ʰᶜ : (AnnTerm × AnnTerm → AnnTerm) → ruleFun AnnTerm 2F
          conv2ʰᶜ f = conv2ʰ (curry f)

          conv3ʰᶜ : (AnnTerm × AnnTerm × AnnTerm → AnnTerm) → ruleFun AnnTerm 3F
          conv3ʰᶜ f = conv3ʰ (λ x → curry (curry f x))

          convᵇ : (String → AnnTerm → AnnTerm → AnnTerm) → ruleFun AnnTerm 3F
          convᵇ f n y y' = do n ← toName n; y ← helper accu y; y' ← helper (n ∷ accu) y'; return $ f n y y'

      in ruleCaseN y "term"
        (("_var_" , 1F , (λ x → ruleCaseN x "var"
          (("_string_" , 1F , λ n → do
            n' ← toName n
            return $ case findIndexList (n' ≣_) accu of λ where
              (just x) → BoundVar $ fromℕ x
              nothing  → FreeVar n') ∷
          ("_index_" , 1F , (λ n → BoundVar ∘ fromℕ <$> toIndex n)) ∷ []))) ∷

        ("_sort_" , 1F , toSort) ∷

        ("π^space^_term_" , 1F , conv1ʰ Pr1-A) ∷
        ("ψ^space^_term_" , 1F , conv1ʰ Pr2-A) ∷

        ("β^space^_term_^space^_term_" , 2F , conv2ʰ Beta-A) ∷
        ("δ^space^_term_^space^_term_" , 2F , conv2ʰ Delta-A) ∷
        ("σ^space^_term_" , 1F , conv1ʰ Sigma-A) ∷

        ("[^space'^_term_^space^_term_^space'^]" , 2F , conv2ʰ App-A) ∷
        ("<^space'^_term_^space^_term_^space'^>" , 2F , conv2ʰ AppE-A) ∷

        ("ρ^space^_term_^space^_string_^space^" , 4F , (λ y n' y' y'' → do
          t ← helper accu y
          n ← toName n'
          t' ← helper (n ∷ accu) y'
          t'' ← helper accu y''
          return $ Rho-A t t' t'')) ∷

        ("∀^space^_string_^space'^:^space'^_term_^space^_term_" , 3F , convᵇ All-A) ∷
        ("Π^space^_string_^space'^:^space'^_term_^space^_term_" , 3F , convᵇ Pi-A) ∷
        ("ι^space^_string_^space'^:^space'^_term_^space^_term_" , 3F , convᵇ Iota-A) ∷
        ("λ^space^_string_^space'^:^space'^_term_^space^_term_" , 3F , convᵇ Lam-A) ∷
        ("Λ^space^_string_^space'^:^space'^_term_^space^_term_" , 3F , convᵇ LamE-A) ∷

        ("{^space'^_term_^space'^,^space'^_term_^space^_string_^space'^.^space'^_term_^space'^}" , 4F , (λ y y' n y'' → do
          t ← helper accu y
          t' ← helper accu y'
          n ← toName n
          t'' ← helper (n ∷ accu) y''
          return $ Rho-A t t' t'')) ∷

        ("φ^space^_term_^space^_term_^space^_term_" , 3F , conv3ʰ Phi-A) ∷
        ("=^space^_term_^space^_term_" , 2F , conv2ʰ Eq-A) ∷
        ("ω^space^_term_" , 1F , conv1ʰ M-A) ∷
        ("μ^space^_term_^space^_term_" , 2F , conv2ʰ Mu-A) ∷
        ("ε^space^_term_" , 1F , conv1ʰ Epsilon-A) ∷

        ("ζLet^space^_term_^space^_term_" , 2F , conv2ʰᶜ (Ev-A Let)) ∷
        ("ζAnnLet^space^_term_^space^_term_^space^_term_" , 3F , conv3ʰᶜ (Ev-A AnnLet)) ∷
        ("ζSetEval^space^_term_^space^_term_^space^_term_" , 3F , conv3ʰᶜ (Ev-A SetEval)) ∷
        ("ζShellCmd^space^_term_^space^_term_" , 2F , conv2ʰᶜ (Ev-A ShellCmd)) ∷
        ("ζCheckTerm^space^_term_^space^_term_" , 2F , conv2ʰᶜ (Ev-A CheckTerm)) ∷
        ("ζParse^space^_term_^space^_term_^space^_term_" , 3F , conv3ʰᶜ (Ev-A Parse)) ∷
        ("ζCatchErr^space^_term_^space^_term_" , 2F , conv2ʰ Gamma-A) ∷
        ("ζNormalize^space^_term_" , 1F , conv1ʰ (Ev-A Normalize)) ∷
        ("ζHeadNormalize^space^_term_" , 1F , conv1ʰ (Ev-A HeadNormalize)) ∷
        ("ζInferType^space^_term_" , 1F , conv1ʰ (Ev-A InferType)) ∷
        ("ζImport^space^_term_" , 1F , conv1ʰ (Ev-A Import)) ∷

        ("Κ_const_" , 1F , (λ z → Const-A <$> toConst z)) ∷
        ("κ_char_" , 1F , (λ z → Char-A <$> toChar z <∣> toChar' z)) ∷

        ("γ^space^_term_^space^_term_" , 2F , conv2ʰ CharEq-A) ∷ [])

data BootstrapStmt : Set where
  Let           : GlobalName → AnnTerm → Maybe AnnTerm → BootstrapStmt
  SetEval       : AnnTerm → String → String → BootstrapStmt
  Empty         : BootstrapStmt

instance
  BootstrapStmt-Show : Show BootstrapStmt
  BootstrapStmt-Show = record { show = helper }
    where
      helper : BootstrapStmt → String
      helper (Let x x₁ (just x₂)) = "let " + x + " := " + show x₁ + " : " + show x₂
      helper (Let x x₁ nothing)   = "let " + x + " := " + show x₁
      helper (SetEval x n n')     = "seteval " + show x + " " + n + " " + n'
      helper Empty                = "Empty"

private
  toBootstrapStmt : PTree → Maybe BootstrapStmt
  toBootstrapStmt (Node x (x' ∷ [])) =
    if x ≡ᴹ ruleId "stmt" "^space'^_stmt'_"
      then ruleCaseN x' "stmt'"
        (("let^space^_string_^space'^:=^space'^_term_^space'^_lettail_" , 3F , λ y y' y'' →
          do y ← toName y; y' ← toTerm y'; y'' ← toLetTail y''; return $ Let y y' y'') ∷
        ("seteval^space^_term_^space^_string_^space^_string_^space'^." , 3F , λ y y' y'' →
          do y ← toTerm y; y' ← toName y'; y'' ← toName y''; return $ SetEval y y' y'') ∷ [])
      else nothing
    where
      toLetTail : PTree → Maybe (Maybe AnnTerm)
      toLetTail x = ruleCaseN x "lettail"
        ((":^space'^_term_^space'^." , 1F , λ y → just <$> toTerm y) ∷ ("." , 0F , just nothing) ∷ [])

  toBootstrapStmt _ = nothing

module _ {M} {{_ : Monad M}} {{_ : MonadExcept M String}} where

  preCoreGrammar : M Grammar
  preCoreGrammar = generateCFGNonEscaped "stmt" coreGrammarGenerator

  private
    parseToConstrTree : (G : Grammar) → NonTerminal G → String → M (Tree (String ⊎ Char) × String)
    parseToConstrTree (_ , G , (showRule , showNT)) S s = do
      (t , rest) ← parseWithInitNT showNT matchMulti show G M S s
      return (_<$>_ {{Tree-Functor}} (Data.Sum.map₁ showRule) t , rest)

  -- Parse the next top-level non-terminal symbol from a string, and return a
  -- term representing the result of the parse, as well as the unparsed rest of
  -- the string
  {-# TERMINATING #-}
  parse : (G : Grammar) → NonTerminal G → String → String → M (AnnTerm × String)
  parse G S namespace s = map₁ (foldConstrTree namespace) <$> parseToConstrTree G S s
    where
      -- Folds a tree of constructors back into a term by properly applying the
      -- constructors and prefixing the namespace
      foldConstrTree : String → Tree (String ⊎ Char) → AnnTerm
      foldConstrTree namespace (Node x x₁) =
        foldl _⟪$⟫_ (ruleToTerm x) (foldConstrTree namespace <$> x₁)
          where
            ruleToTerm : String ⊎ Char → AnnTerm
            ruleToTerm (inj₁ x) = FreeVar (namespace + "$" + ruleToConstr x)
            ruleToTerm (inj₂ y) = Char-A y

  -- Used for bootstrapping
  {-# TERMINATING #-} -- cannot just use sequence in synTreetoℕtree because of the char special case
  parseBootstrap : Grammar → String → M (BootstrapStmt × String)
  parseBootstrap G s = do
    (y' , rest) ← parseToConstrTree G (initNT G) s
    y ← synTreeToℕTree y'
    case toBootstrapStmt y of λ where
      (just x) → return (x , rest)
      nothing → throwError ("Error while converting syntax tree to statement!\nTree:\n" + show y'
                             + "\nRemaining: " + s)
    where
      convertIfChar : Tree (String ⊎ Char) → Maybe PTree
      convertIfChar (Node (inj₁ x) x₁) = do
        rest ← stripPrefix "nameInitChar$" x <∣> stripPrefix "nameTailChar$" x
        (c , s) ← uncons rest
        just $ Node (inj₂ $ unescape c s) []
      convertIfChar (Node (inj₂ x) x₁) = nothing

      synTreeToℕTree : Tree (String ⊎ Char) → M PTree
      synTreeToℕTree t@(Node (inj₁ x) x₁) with convertIfChar t
      ... | (just t') = return t'
      ... | nothing = do
        id ← fullRuleId x
        ids ← sequence $ map synTreeToℕTree x₁
        return (Node id ids)
        where
          fullRuleId : String → M (ℕ ⊎ Char)
          fullRuleId l with break (_≟ '$') (toList l) -- split at '$'
          ... | (x , []) = throwError "No '$' character found!"
          ... | (x , _ ∷ y) = maybeToError (ruleId (fromList x) (fromList y)) ("Rule " + l + "doesn't exist!")

      synTreeToℕTree (Node (inj₂ x) x₁) = return $ Node (inj₂ x) []
