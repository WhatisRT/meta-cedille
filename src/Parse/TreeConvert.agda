--------------------------------------------------------------------------------
-- This file contains functions to turn the tree of parse results into the agda
-- data structures they represent.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Parse.TreeConvert where

import Data.Sum
open import Data.Fin using (fold; toℕ)
open import Class.Map
open import Class.Monad.Except
open import Data.Map.String
open import Data.String as S using (fromList; toList; fromChar; uncons)
open import Data.Tree
open import Data.Tree.Instance
open import Data.Word using (fromℕ)
open import Data.Vec.Recursive using (_^_)
open import Class.Listable

open import Prelude hiding (_^_)

open import Bootstrap.InitEnv
open import Parse.Escape
open import Parse.Generate
open import Parse.LL1
open import Parse.MultiChar
open import Theory.TypeChecking

PTree : Set
PTree = Tree (ℕ ⊎ Char)

RuleType : Set
RuleType = Fin 5

ruleFun' : ∀ {k} → Set → Fin k → Set
ruleFun' A = fold _ (λ T → PTree → T) (Maybe A)

ruleFun = ruleFun' {k = 5}

ruleIdMap : StringMap (StringMap ℕ)
ruleIdMap = mapSnd (fromListSM ∘ mapWithIndex (flip _,_)) $ fromListSM parseRuleMap

ruleId : String → String → Maybe (ℕ ⊎ Char)
ruleId nonterm rule = inj₁ <$> (lookup rule =<< lookup nonterm ruleIdMap)

_≡ᴹ_ : ℕ ⊎ Char → Maybe (ℕ ⊎ Char) → Bool
x ≡ᴹ y = just x ≣ y

ruleIdN : ∀ {A k} → (n : Fin k) → String → String → ruleFun' A n → List PTree → Maybe (ℕ ⊎ Char) × Maybe A
ruleIdN 0F      s s' f []       = (ruleId s s' , f)
ruleIdN (suc n) s s' f (x ∷ xs) = (ruleIdN n s s' (f x) xs)
ruleIdN _       s s' _ _        = (ruleId s s' , nothing)

ruleCaseN : {A : Set} → PTree → String → List (String × Σ[ t ∈ RuleType ] ruleFun A t) → Maybe A
ruleCaseN (Node x x₁) r cs =
  decCase just x of map (λ where (x , t , f) → ruleIdN t r x f x₁) cs default nothing

toSort : PTree → Maybe AnnTerm
toSort x = ruleCaseN x "sort" (("=ast=" , 0F , just ⋆) ∷ ("=sq=" , 0F , just □) ∷ [])

toChar : PTree → Maybe Char
toChar (Node (inj₁ x) x₁) = nothing
toChar (Node (inj₂ y) x₁) = just y

toChar' : PTree → Maybe Char
toChar' x = ruleCaseN x "char" (("!!" , 1F , toChar) ∷ [])

toConst : PTree → Maybe Const
toConst x = ruleCaseN x "const" $
  ("CharT"         , 0F , just CharT) ∷
  ("=kappa=_char_" , 1F , (λ z → CharC <$> toChar z <∣> toChar' z)) ∷
  ("CharEq"        , 0F , just CharEq) ∷
  ("MM"            , 0F , just MM) ∷
  ("MuM"           , 0F , just MuM) ∷
  ("EpsilonM"      , 0F , just EpsilonM) ∷
  ("CatchM"        , 0F , just CatchM) ∷ []

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
      let ruleFun'' : ∀ {k} → Set → Fin k → Set
          ruleFun'' A = fold _ (λ T → PTree → T) (Maybe A)

          conv0ʰ : (⊤ → AnnTerm) → ruleFun AnnTerm 0F
          conv0ʰ f = f <$> (just _)

          conv1ʰ : (AnnTerm → AnnTerm) → ruleFun AnnTerm 1F
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

          primRule : PrimMeta → String × Σ[ k ∈ RuleType ] ruleFun AnnTerm k
          primRule m =
            let convk = case_return_of_ (primMetaArityF m)
                          (λ k → (AnnTerm ^ (toℕ k) → AnnTerm) → ruleFun AnnTerm k) λ where
                  0F → conv0ʰ ; 1F → conv1ʰ ; 2F → conv2ʰᶜ ; 3F → conv3ʰᶜ
                  4F → λ _ _ _ _ _ → nothing -- currently unncessary
            in (genBuiltin' m , primMetaArityF m , convk (Ev m))

      in ruleCaseN y "term"
        (("_var_" , 1F , (λ x → ruleCaseN x "var"
          (("_string_" , 1F , λ n → do
            n' ← toName n
            return $ case findIndexList (n' ≣_) accu of λ where
              (just x) → BoundVar $ fromℕ x
              nothing  → FreeVar n') ∷
          ("_index_" , 1F , (λ n → BoundVar ∘ fromℕ <$> toIndex n)) ∷ []))) ∷

        ("_sort_" , 1F , toSort) ∷

        (genSimple "=pi="  1 , 1F , conv1ʰ Pr1) ∷ (genSimple "=psi=" 1 , 1F , conv1ʰ Pr2) ∷

        (genSimple "=beta="  2 , 2F , conv2ʰ Beta) ∷
        (genSimple "=delta=" 2 , 2F , conv2ʰ Delta) ∷
        (genSimple "=sigma=" 1 , 1F , conv1ʰ Sigma) ∷

        (genSimple "=phi="   3 , 3F , conv3ʰ Phi) ∷ (genSimple "=equal=" 2 , 2F , conv2ʰ Eq-T) ∷

        ("=lsquare=^space'^_term_^space^_term_^space'^=rsquare=" , 2F , conv2ʰ (App Regular)) ∷
        ("=langle=^space'^_term_^space^_term_^space'^=rangle="   , 2F , conv2ʰ (App Erased)) ∷

        ("=rho=^space^_term_^space^_string_^space'^=dot=^space'^_term_^space^_term_" , 4F , (λ y n' y' y'' → do
          t ← helper accu y
          n ← toName n'
          t' ← helper (n ∷ accu) y'
          t'' ← helper accu y''
          return $ Rho t t' t'')) ∷

        (genBinder "=forall=" , 3F , convᵇ (Pi Erased)) ∷
        (genBinder "=Pi="     , 3F , convᵇ (Pi Regular)) ∷
        (genBinder "=iota="   , 3F , convᵇ Iota) ∷
        (genBinder "=lambda=" , 3F , convᵇ (Lam-A Regular)) ∷
        (genBinder "=Lambda=" , 3F , convᵇ (Lam-A Erased)) ∷

        ("=lbrace=^space'^_term_^space'^=comma=^space'^_term_^space^_string_^space'^=dot=^space'^_term_^space'^=rbrace=" , 4F , (λ y y' n y'' → do
          t ← helper accu y
          t' ← helper accu y'
          n ← toName n
          t'' ← helper (n ∷ accu) y''
          return $ Pair t t' t'')) ∷

        (genSimple "=omega="   1 , 1F , conv1ʰ M-T) ∷
        (genSimple "=mu="      2 , 2F , conv2ʰ Mu) ∷
        (genSimple "=epsilon=" 1 , 1F , conv1ʰ Epsilon) ∷

        map primRule (Listable.listing PrimMeta-Listable) ++

        ("=Kappa=_const_" , 1F , (λ z → Const-T <$> toConst z)) ∷ [])

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
        (("let^space^_string_^space'^=colon==equal=^space'^_term_^space'^_lettail_" , 3F , λ y y' y'' →
          do y ← toName y; y' ← toTerm y'; y'' ← toLetTail y''; return $ Let y y' y'') ∷
        ("seteval^space^_term_^space^_string_^space^_string_^space'^=dot=" , 3F , λ y y' y'' →
          do y ← toTerm y; y' ← toName y'; y'' ← toName y''; return $ SetEval y y' y'') ∷ [])
      else nothing
    where
      toLetTail : PTree → Maybe (Maybe AnnTerm)
      toLetTail x = ruleCaseN x "lettail"
        (("=colon=^space'^_term_^space'^=dot=" , 1F , λ y → just <$> toTerm y) ∷ ("=dot=" , 0F , just nothing) ∷ [])

  toBootstrapStmt _ = nothing

module _ {M} {{_ : Monad M}} {{_ : MonadExcept M String}} where

  preCoreGrammar : M Grammar
  preCoreGrammar = generateCFG "stmt" grammarWithChars

  private
    parseToConstrTree : (G : Grammar) → NonTerminal G → String → M (Tree (String ⊎ Char) × String × String)
    parseToConstrTree (_ , G , (showRule , showNT)) S s = do
      (t , rest) ← parseWithInitNT showNT matchMulti show G M S s
      return (_<$>_ {{Tree-Functor}} (Data.Sum.map₁ (ruleToConstr ∘ showRule)) t
             , strTake (S.length s ∸ S.length rest) s , rest)

  -- Parse the next top-level non-terminal symbol from a string, and return a
  -- term representing the result of the parse, as well as the unparsed rest of
  -- the string
  {-# TERMINATING #-}
  parse : (G : Grammar) → NonTerminal G → String → String → M (AnnTerm × String × String)
  parse G S namespace s = map₁ (foldConstrTree namespace) <$> parseToConstrTree G S s
    where
      -- Folds a tree of constructors back into a term by properly applying the
      -- constructors and prefixing the namespace
      foldConstrTree : String → Tree (String ⊎ Char) → AnnTerm
      foldConstrTree namespace (Node x x₁) =
        foldl _⟪$⟫_ (ruleToTerm x) (foldConstrTree namespace <$> x₁)
          where
            ruleToTerm : String ⊎ Char → AnnTerm
            ruleToTerm (inj₁ x) = FreeVar (namespace + "$" + x)
            ruleToTerm (inj₂ y) = Const-T (CharC y)

  -- Used for bootstrapping
  {-# TERMINATING #-} -- cannot just use sequence in synTreetoℕtree because of the char special case
  parseBootstrap : Grammar → String → M (BootstrapStmt × String × String)
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
        rest ← translateS =<< (stripPrefix "nameInitChar$" x <∣> stripPrefix "nameTailChar$" x)
        (c , _) ← uncons rest
        just $ Node (inj₂ c) []
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
          ... | (x , _ ∷ y) = maybeToError (ruleId (fromList x) (fromList y))
                                           ("Rule " + l + " doesn't exist!")

      synTreeToℕTree (Node (inj₂ x) x₁) = return $ Node (inj₂ x) []
