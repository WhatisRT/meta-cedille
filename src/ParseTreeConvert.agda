--------------------------------------------------------------------------------
-- This file contains functions to turn the tree of parse results into the agda
-- data structures they represent.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module ParseTreeConvert where

import Data.Product
import Data.Sum
open import Agda.Builtin.Nat using (_-_)
open import Class.Map
open import Class.Monad.Except
open import Class.Traversable
open import Data.Char using (toNat)
open import Data.Fin.Instance
open import Data.List using (break)
open import Data.Maybe using () renaming (_<∣>_ to addMaybe)
open import Data.SimpleMap
open import Data.String using (fromList; toList; fromChar)
open import Data.Tree
open import Data.Tree.Instance
open import Data.Word using (fromℕ)
open import Data.Word32
open import Relation.Nullary

open import Prelude
open import Prelude.Strings

open import CoreTheory
open import InitEnv
open import Parser
open import ParserGenerator

-- accepts the head and tail of a string and returns the head of the full string without escape symbols
unescape : Char → String → Char
unescape c r = if ⌊ c ≟ '\\' ⌋ then (case strHead r of λ { nothing → c ; (just x) → x}) else c

continueIfInit : ∀ {a} {A : Set a} → List Char → List Char → (List Char → A) → Maybe A
continueIfInit {A = A} init s = helper init s
  where
    helper : List Char → List Char → (List Char → A) → Maybe A
    helper [] s f = just $ f s
    helper (x₁ ∷ init) [] f = nothing
    helper (x₁ ∷ init) (x ∷ s) f with x ≟ x₁
    ... | yes p = helper init s f
    ... | no ¬p = nothing

ruleId : List Char → List Char → Maybe (ℕ ⊎ Char)
ruleId nonterm rule = do
  rules ← lookup nonterm parseRuleMap
  i ← findIndexList (_≟ (nonterm + "$" + rule)) rules
  return $ inj₁ i

instance
   _ = Eq→EqB

_≡ᴹ_ : ℕ ⊎ Char → Maybe (ℕ ⊎ Char) → Bool
x ≡ᴹ y = just x ≣ y

toSort : Tree (ℕ ⊎ Char) → Maybe Sort
toSort (Node x x₁) =
  if x ≡ᴹ ruleId "sort" "*"
    then return ⋆
    else if x ≡ᴹ ruleId "sort" "□"
      then return □
      else nothing

toConst : Tree (ℕ ⊎ Char) → Maybe Const
toConst (Node x x₁) =
  if x ≡ᴹ ruleId "const" "Char"
    then return CharT
    else nothing

toChar : Tree (ℕ ⊎ Char) → Maybe Char
toChar (Node (inj₁ x) x₁) = nothing
toChar (Node (inj₂ y) x₁) = just y

toChar' : Tree (ℕ ⊎ Char) → Maybe Char
toChar' (Node x x₁) =
  if x ≡ᴹ ruleId "char" "!!"
    then (case x₁ of λ { (y ∷ []) → toChar y ; _ → nothing })
    else nothing

toName : Tree (ℕ ⊎ Char) → Maybe String
toName (Node x x₁) = case x₁ of λ
  { (y ∷ y' ∷ _) → do
    c ← toChar y
    n ← toName y'
    return (fromChar c + n)
  ; [] → if x ≡ᴹ ruleId "string'" ""
      then return ""
      else nothing
  ; _ → nothing }

toNameList : Tree (ℕ ⊎ Char) → Maybe (List String)
toNameList (Node x []) = just []
toNameList (Node x (x₁ ∷ x₂ ∷ _)) = do
  n ← toName x₁
  rest ← toNameList x₂
  return $ n ∷ rest
{-# CATCHALL #-}
toNameList _ = nothing

toIndex : Tree (ℕ ⊎ Char) → Maybe ℕ
toIndex t = do
  res ← helper t
  foldl {A = Maybe ℕ} (λ x c → (λ x' → 10 * x' + c) <$> x) (just 0) res
  where
    helper' : Tree (ℕ ⊎ Char) → Maybe (List ℕ)
    helper' (Node x []) =
      if x ≡ᴹ ruleId "index'" ""
        then return []
        else nothing
    helper' (Node x (x₁ ∷ _)) = do
      rest ← helper' x₁
      decCase (just x) of
        (ruleId "index'" "0_index'_" , return (0 ∷ rest)) ∷
        (ruleId "index'" "1_index'_" , return (1 ∷ rest)) ∷
        (ruleId "index'" "2_index'_" , return (2 ∷ rest)) ∷
        (ruleId "index'" "3_index'_" , return (3 ∷ rest)) ∷
        (ruleId "index'" "4_index'_" , return (4 ∷ rest)) ∷
        (ruleId "index'" "5_index'_" , return (5 ∷ rest)) ∷
        (ruleId "index'" "6_index'_" , return (6 ∷ rest)) ∷
        (ruleId "index'" "7_index'_" , return (7 ∷ rest)) ∷
        (ruleId "index'" "8_index'_" , return (8 ∷ rest)) ∷
        (ruleId "index'" "9_index'_" , return (9 ∷ rest)) ∷ []
        default nothing

    helper : Tree (ℕ ⊎ Char) → Maybe (List ℕ)
    helper (Node x []) = nothing
    helper (Node x (x₁ ∷ _)) = do
      rest ← helper' x₁
      decCase just x of
        (ruleId "index" "0_index'_" , return (0 ∷ rest)) ∷
        (ruleId "index" "1_index'_" , return (1 ∷ rest)) ∷
        (ruleId "index" "2_index'_" , return (2 ∷ rest)) ∷
        (ruleId "index" "3_index'_" , return (3 ∷ rest)) ∷
        (ruleId "index" "4_index'_" , return (4 ∷ rest)) ∷
        (ruleId "index" "5_index'_" , return (5 ∷ rest)) ∷
        (ruleId "index" "6_index'_" , return (6 ∷ rest)) ∷
        (ruleId "index" "7_index'_" , return (7 ∷ rest)) ∷
        (ruleId "index" "8_index'_" , return (8 ∷ rest)) ∷
        (ruleId "index" "9_index'_" , return (9 ∷ rest)) ∷ []
        default nothing

toTerm : Tree (ℕ ⊎ Char) → Maybe AnnTerm
toTerm = helper []
  where
    helper : List String → Tree (ℕ ⊎ Char) → Maybe AnnTerm
    helper accu (Node x x₁) =
      decCase just x of
      
        (ruleId "term" "_var_" , (case x₁ of λ
          { ((Node y (n ∷ [])) ∷ []) →
            decCase just y of
              (ruleId "var" "_string_" , do
                n' ← toName n
                return $ case findIndexList (n' ≟_) accu of λ
                  { (just x) → BoundVar $ fromℕ x
                  ; nothing → FreeVar n' }) ∷
              (ruleId "var" "_index_" , do
                n' ← toIndex n
                return $ BoundVar $ fromℕ n') ∷ []
            default nothing
          ; _ → nothing })) ∷

        (ruleId "term" "_sort_" , do
          s ← head x₁ >>= toSort
          return $ Sort-A s) ∷

        (ruleId "term" "π_space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ []) → do
            y' ← helper accu y
            return $ Pr1-A y'
          ; _ → nothing })) ∷

        (ruleId "term" "ψ_space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ []) → do
            y' ← helper accu y
            return $ Pr2-A y'
          ; _ → nothing })) ∷

        (ruleId "term" "β_space__term__space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ []) → do
            t ← helper accu y
            t' ← helper accu y'
            return $ Beta-A t t'
          ; _ → nothing })) ∷

        (ruleId "term" "δ_space__term__space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ []) → do
            t ← helper accu y
            t' ← helper accu y'
            return $ Delta-A t t'
          ; _ → nothing })) ∷

        (ruleId "term" "σ_space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ []) → helper accu y >>= λ y' → return (Sigma-A y') ; _ → nothing })) ∷

        (ruleId "term" "[_space'__term__space__term__space'_]" , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ []) → do
            t ← helper accu y
            t' ← helper accu y'
            return $ App-A t t'
          ; _ → nothing })) ∷

        (ruleId "term" "<_space'__term__space__term__space'_>" , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ []) → do
            t ← helper accu y
            t' ← helper accu y'
            return $ AppE-A t t'
          ; _ → nothing })) ∷

        (ruleId "term"
          "ρ_space__term__space__string__space'_._space'__term__space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ n' ∷ _ ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) → do
            t ← helper accu y
            n ← toName n'
            t' ← helper (n ∷ accu) y'
            t'' ← helper accu y''
            return $ Rho-A t t' t''
          ; _ → nothing })) ∷

        (ruleId "term"
          "∀_space__string__space'_:_space'__term__space__term_" , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) → do
            n ← toName n'
            t ← helper accu y
            t' ← helper (n ∷ accu) y'
            return $ All-A n t t'
          ; _ → nothing })) ∷

        (ruleId "term"
          "Π_space__string__space'_:_space'__term__space__term_" , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) → do
            n ← toName n'
            t ← helper accu y
            t' ← helper (n ∷ accu) y'
            return $ Pi-A n t t'
          ; _ → nothing })) ∷

        (ruleId "term"
          "ι_space__string__space'_:_space'__term__space__term_" , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) → do
            n ← toName n'
            t ← helper accu y
            t' ← helper (n ∷ accu) y'
            return $ Iota-A n t t'
          ; _ → nothing })) ∷

        (ruleId "term"
          "λ_space__string__space'_:_space'__term__space__term_" , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) → do
            n ← toName n'
            t ← helper accu y
            t' ← helper (n ∷ accu) y'
            return $ Lam-A n t t'
          ; _ → nothing })) ∷

        (ruleId "term"
          "Λ_space__string__space'_:_space'__term__space__term_" , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) → do
            n ← toName n'
            t ← helper accu y
            t' ← helper (n ∷ accu) y'
            return $ LamE-A n t t'
          ; _ → nothing })) ∷

        (ruleId "term"
          "{_space'__term__space'_,_space'__term__space__string__space'_._space'__term__space'_}" ,
          (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ _ ∷ y' ∷ _ ∷ n' ∷ _ ∷ _ ∷ y'' ∷ _ ∷ []) → do
            t ← helper accu y
            t' ← helper accu y'
            n ← toName n'
            t'' ← helper (n ∷ accu) y''
            return $ Pair-A t t' t''
          ; _ → nothing })) ∷

        (ruleId "term" "φ_space__term__space__term__space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) → do
            t ← helper accu y
            t' ← helper accu y'
            t'' ← helper accu y''
            return $ Phi-A t t' t''
          ; _ → nothing })) ∷

        (ruleId "term" "=_space__term__space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ []) → do
            t ← helper accu y
            t' ← helper accu y'
            return $ Eq-A t t'
          ; _ → nothing })) ∷

        (ruleId "term" "ω_space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ []) → do
            t ← helper accu y
            return $ M-A t
          ; _ → nothing })) ∷

        (ruleId "term" "μ_space__term__space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ []) → do
            t ← helper accu y
            t' ← helper accu y'
            return $ Mu-A t t'
          ; _ → nothing })) ∷

        (ruleId "term" "ε_space__term_" , (case x₁ of λ
          { (_ ∷ y ∷ []) → do
            t ← helper accu y
            return $ Epsilon-A t
          ; _ → nothing })) ∷

        (ruleId "term" "Α_space__term_" , (case x₁ of λ -- alpha
          { (_ ∷ z ∷ []) → do
            t ← helper accu z
            return $ Ev-A EvalStmt t
          ; _ → nothing })) ∷

        (ruleId "term" "Β_space__term__space__term_" , (case x₁ of λ -- beta
          { (_ ∷ z ∷ _ ∷ z' ∷ []) → do
            t ← helper accu z
            t' ← helper accu z'
            return $ Ev-A ShellCmd (t , t')
          ; _ → nothing })) ∷

        (ruleId "term" "Γ_space__term__space__term_" , (case x₁ of λ
          { (_ ∷ z ∷ _ ∷ z' ∷ []) → do
            t ← helper accu z
            t' ← helper accu z'
            return $ Ev-A CatchErr (t , t')
          ; _ → nothing })) ∷

        (ruleId "term" "Δ_space__term__space__term_" , (case x₁ of λ
          { (_ ∷ z ∷ _ ∷ z' ∷ []) → do
            t ← helper accu z
            t' ← helper accu z'
            return $ Ev-A CheckTerm (t , t')
          ; _ → nothing })) ∷

        (ruleId "term" "Κ_const_" , (case x₁ of λ
          { (z ∷ []) → do
            c ← toConst z
            return $ Const-A c
          ; _ → nothing })) ∷

        (ruleId "term" "κ_char_" , (case x₁ of λ
          { (z ∷ []) → do
            c ← addMaybe (toChar z) (toChar' z)
            return $ Char-A c
          ; _ → nothing })) ∷

        (ruleId "term" "γ_space__term__space__term_" , (case x₁ of λ
          { (_ ∷ z ∷ _ ∷ z' ∷ []) → do
            t ← helper accu z
            t' ← helper accu z'
            return $ CharEq-A t t'
          ; _ → nothing })) ∷

        []
        default nothing

data Stmt : Set where
  Let : GlobalName → AnnTerm → Maybe AnnTerm → Stmt
  Ass : GlobalName → AnnTerm → Stmt
  Normalize : AnnTerm → Stmt
  HeadNormalize : AnnTerm → Stmt
  EraseSt : AnnTerm → Stmt
  Test : AnnTerm → Stmt
  SetEval : AnnTerm → String → String → Stmt
  Import : String → Stmt
  Shell : String → Stmt
  Empty : Stmt

instance
  Stmt-Show : Show Stmt
  Stmt-Show = record { show = helper }
    where
      helper : Stmt → String
      helper (Let x x₁ (just x₂)) = "let " + x + " := " + show x₁ + " : " + show x₂
      helper (Let x x₁ nothing) = "let " + x + " := " + show x₁
      helper (Ass x x₁) = "ass " + x + " : " + show x₁
      helper (Normalize x) = "normalize " + show x
      helper (HeadNormalize x) = "normalize " + show x
      helper (EraseSt x) = "erase " + show x
      helper (Test x) = "test " + show x
      helper (SetEval x n n') = "seteval " + show x + " " + n + " " + n'
      helper (Import s) = "import " + s
      helper (Shell x) = "shell \"" + show x + "\""
      helper Empty = "Empty"

toStmt : Tree (ℕ ⊎ Char) → Maybe Stmt
toStmt (Node x (_ ∷ (Node x' x₂) ∷ [])) =
  if x ≡ᴹ ruleId "stmt" "_space'__stmt'_"
    then
      decCase just x' of
        (ruleId "stmt'" "let_space__string__space'_:=_space'__term__space'__lettail_" ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) → do
              n ← toName y
              t ← toTerm y'
              return $ Let n t $ toLetTail y''
            ; _ → nothing })) ∷

        (ruleId "stmt'"
          "ass_space__string__space'_:_space'__term__space'_." ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ _ ∷ y₁ ∷ _ ∷ []) → do
              n ← toName y
              t ← toTerm y₁
              return $ Ass n t
            ; _ → nothing })) ∷

        (ruleId "stmt'" "normalize_space__term__space'_." ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) → do
              t ← toTerm y
              return $ Normalize t
            ; _ → nothing })) ∷

        (ruleId "stmt'" "hnf_space__term__space'_." ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) → do
              t ← toTerm y
              return $ HeadNormalize t
            ; _ → nothing })) ∷

        (ruleId "stmt'" "erase_space__term__space'_." ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) → do
              t ← toTerm y
              return $ EraseSt t
            ; _ → nothing })) ∷

        (ruleId "stmt'" "test_space__term__space'_." ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) → do
              t ← toTerm y
              return $ Test t
            ; _ → nothing })) ∷

        (ruleId "stmt'" "seteval_space__term__space__string__space__string__space'_." ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ y'' ∷ _ ∷ []) → do
              t ← toTerm y
              n ← toName y'
              n' ← toName y''
              return $ SetEval t n n'
            ; _ → nothing })) ∷

        (ruleId "stmt'" "import_space__string__space'_." ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) → do
              n ← toName y
              return $ Import n
            ; _ → nothing })) ∷

        (ruleId "stmt'" "cmd_space__string__space'_." ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) → do
              n ← toName y
              return $ Shell n
            ; _ → nothing })) ∷

        (ruleId "stmt'" "" ,
          return Empty) ∷

        []
      default nothing
    else nothing

  where
    toLetTail : Tree (ℕ ⊎ Char) → Maybe AnnTerm
    toLetTail (Node x x₁) =
      decCase just x of
        (ruleId "lettail" ":_space'__term__space'_." ,
          (case x₁ of λ
            { (_ ∷ y ∷ _ ∷ []) → toTerm y
            ; _ → nothing })) ∷
        []
      default nothing

{-# CATCHALL #-}
toStmt _ = nothing

module _ {M} {{_ : Monad M}} {{_ : MonadExcept M String}} where

  preCoreGrammar : M Grammar
  preCoreGrammar = generateCFG "stmt" (map fromList coreGrammarGenerator)

  parse' : Grammar → String → M (Tree (String ⊎ Char) × String)
  parse' (fst , fst₁ , snd) s = do
    res ← LL1Parser.parse (proj₂ snd) matchMulti show fst₁ M s
    return (Data.Product.map₁ (_<$>_ {{Tree-Functor}} (Data.Sum.map₁ (proj₁ snd))) res)

  parse : String → M (Tree (String ⊎ Char) × String)
  parse s = do
    G ← preCoreGrammar
    parse' G s

  {-# TERMINATING #-} -- cannot just use sequence here because of the char special case
  synTreeToℕTree : Tree (String ⊎ Char) → M (Tree (ℕ ⊎ Char))
  synTreeToℕTree t@(Node (inj₁ x) x₁) = do
    case convertIfChar t of λ
      { (just t') → return t'
      ; nothing → do
        id ← fullRuleId x
        ids ← sequence $ map synTreeToℕTree x₁
        return (Node id ids)
      }
    where
      fullRuleId : String → M (ℕ ⊎ Char)
      fullRuleId l with break (_≟ '$') (toList l) -- split at '$'
      ... | (x , []) = throwError "No '$' character found!"
      ... | (x , _ ∷ y) = maybeToError (ruleId x y) ("Rule " + l + "doesn't exist!")

      convertIfChar : Tree (String ⊎ Char) → Maybe (Tree (ℕ ⊎ Char))
      convertIfChar (Node (inj₁ x) x₁) = do
        rest ← addMaybe (stripPrefix "nameInitChar$" x) (stripPrefix "nameTailChar$" x)
        (c , s) ← uncons rest
        just $ Node (inj₂ $ unescape c s) []
      convertIfChar (Node (inj₂ x) x₁) = nothing

  synTreeToℕTree (Node (inj₂ x) x₁) = return $ Node (inj₂ x) []

  parseStmt : String → M (Stmt × String)
  parseStmt s = do
    (y' , rest) ← parse s
    y ← synTreeToℕTree y'
    case toStmt y of λ
      { (just x) → return (x , rest)
      ; nothing →
        throwError ("Error while converting syntax tree to statement!\nTree:\n" + show y + "\nRemaining: " + s) }
