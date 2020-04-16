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
open import Data.List hiding (lookup)
open import Data.Maybe using () renaming (_<∣>_ to addMaybe)
open import Data.SimpleMap
open import Data.String using (fromList)
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
unescape : Char -> List Char -> Char
unescape c r = if ⌊ c ≟ '\\' ⌋ then (case r of λ { [] → c ; (x ∷ x₁) → x}) else c

continueIfInit : ∀ {a} {A : Set a} -> List Char -> List Char -> (List Char -> A) -> Maybe A
continueIfInit {A = A} init s = helper init s
  where
    helper : List Char -> List Char -> (List Char -> A) -> Maybe A
    helper [] s f = just $ f s
    helper (x₁ ∷ init) [] f = nothing
    helper (x₁ ∷ init) (x ∷ s) f with x ≟ x₁
    ... | yes p = helper init s f
    ... | no ¬p = nothing

ruleId : List Char -> List Char -> Maybe (ℕ ⊎ Char)
ruleId nonterm rule = do
  rules <- lookup nonterm parseRuleMap
  i <- findIndexList (_≟ (nonterm + "$" + rule)) rules
  return (inj₁ i)

toSort : Tree (ℕ ⊎ Char) -> Maybe Sort
toSort (Node x x₁) =
  if x ≣ (from-just $ ruleId "sort" "*")
    then return ⋆
    else (if x ≣ (from-just $ ruleId "sort" "□")
      then return □
      else nothing)

toConst : Tree (ℕ ⊎ Char) -> Maybe Const
toConst (Node x x₁) =
  if x ≣ (from-just $ ruleId "const" "Char")
    then return CharT
    else nothing

toChar : Tree (ℕ ⊎ Char) -> Maybe Char
toChar (Node (inj₁ x) x₁) = nothing
toChar (Node (inj₂ y) x₁) = just y

toChar' : Tree (ℕ ⊎ Char) -> Maybe Char
toChar' (Node x x₁) =
  if x ≣ (from-just $ ruleId "char" "!!")
    then (case x₁ of λ { (y ∷ []) -> toChar y ; _ -> nothing })
    else nothing

toName : Tree (ℕ ⊎ Char) -> Maybe (List Char)
toName (Node x x₁) = case x₁ of λ
  { (y ∷ y' ∷ _) -> do
    c <- toChar y
    n <- toName' y'
    return (c ∷ n)
  ; _ -> nothing }
  where
    toName' : Tree (ℕ ⊎ Char) -> Maybe (List Char)
    toName' (Node x x₁) = case x₁ of λ
      { (y ∷ y' ∷ _) -> do
        c <- toChar y
        n <- toName' y'
        return (c ∷ n)
      ; [] -> (if x ≣ (from-just $ ruleId "string'" "")
          then return []
          else nothing)
      ; _ -> nothing }

toNameList : Tree (ℕ ⊎ Char) -> Maybe (List String)
toNameList (Node x []) = just []
toNameList (Node x (x₁ ∷ x₂ ∷ _)) = do
  n <- toName x₁
  rest <- toNameList x₂
  return ((fromList n) ∷ rest)
{-# CATCHALL #-}
toNameList _ = nothing

toIndex : Tree (ℕ ⊎ Char) -> Maybe ℕ
toIndex t = do
  res <- helper t
  foldl {A = Maybe ℕ} (λ x c → do
    x' <- x
    return $ 10 * x' + c) (just 0) res
  where
    helper' : Tree (ℕ ⊎ Char) -> Maybe (List ℕ)
    helper' (Node x []) =
      if x ≣ (from-just $ ruleId "index'" "")
        then return []
        else nothing
    helper' (Node x (x₁ ∷ _)) = do
      rest <- helper' x₁
      decCase x of
        ((from-just $ ruleId "index'" "0_index'_") , return (0 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "1_index'_") , return (1 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "2_index'_") , return (2 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "3_index'_") , return (3 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "4_index'_") , return (4 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "5_index'_") , return (5 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "6_index'_") , return (6 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "7_index'_") , return (7 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "8_index'_") , return (8 ∷ rest)) ∷
        ((from-just $ ruleId "index'" "9_index'_") , return (9 ∷ rest)) ∷ []
        default nothing

    helper : Tree (ℕ ⊎ Char) -> Maybe (List ℕ)
    helper (Node x []) = nothing
    helper (Node x (x₁ ∷ _)) = do
      rest <- helper' x₁
      decCase x of
        ((from-just $ ruleId "index" "0_index'_") , return (0 ∷ rest)) ∷
        ((from-just $ ruleId "index" "1_index'_") , return (1 ∷ rest)) ∷
        ((from-just $ ruleId "index" "2_index'_") , return (2 ∷ rest)) ∷
        ((from-just $ ruleId "index" "3_index'_") , return (3 ∷ rest)) ∷
        ((from-just $ ruleId "index" "4_index'_") , return (4 ∷ rest)) ∷
        ((from-just $ ruleId "index" "5_index'_") , return (5 ∷ rest)) ∷
        ((from-just $ ruleId "index" "6_index'_") , return (6 ∷ rest)) ∷
        ((from-just $ ruleId "index" "7_index'_") , return (7 ∷ rest)) ∷
        ((from-just $ ruleId "index" "8_index'_") , return (8 ∷ rest)) ∷
        ((from-just $ ruleId "index" "9_index'_") , return (9 ∷ rest)) ∷ []
        default nothing

toTerm : Tree (ℕ ⊎ Char) -> Maybe AnnTerm
toTerm = helper []
  where
    helper : List (List Char) -> Tree (ℕ ⊎ Char) -> Maybe AnnTerm
    helper accu (Node x x₁) =
      decCase x of
        ((from-just $ ruleId "term" "_var_") ,
          head x₁ >>=
            λ { (Node y (n ∷ [])) ->
                decCase y of
                  ((from-just $ ruleId "var" "_string_") , do
                    n' <- toName n
                    case findIndexList (n' ≟_) accu of (λ
                      { (just x) → return $ Var-A $ Bound $ fromℕ x
                      ; nothing → return $ Var-A $ Free n' })) ∷
                  ((from-just $ ruleId "var" "_index_") , do
                    n' <- toIndex n
                    return $ Var-A $ Bound $ fromℕ n') ∷ []
                default nothing
              ; _ -> nothing }) ∷

        ((from-just $ ruleId "term" "_sort_") , do
          s <- head x₁ >>= toSort
          return (Sort-A s)) ∷

        ((from-just $ ruleId "term" "π_space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ []) -> do
            y' <- helper accu y
            return (y' ∙1)
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "ψ_space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ []) -> do
            y' <- helper accu y
            return (y' ∙2)
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "β_space__term__space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ []) -> do
            t <- helper accu y
            t' <- helper accu y'
            return $ β t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "δ_space__term__space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ []) -> do
            t <- helper accu y
            t' <- helper accu y'
            return $ δ t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "σ_space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ []) -> helper accu y >>= λ y' -> return (ς y') ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "[_space'__term__space__term__space'_]") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ []) -> do
            t <- helper accu y
            t' <- helper accu y'
            return $ App-A t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "<_space'__term__space__term__space'_>") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ []) -> do
            t <- helper accu y
            t' <- helper accu y'
            return $ AppE-A t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "ρ_space__term__space__string__space'_._space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ n' ∷ _ ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) -> do
            t <- helper accu y
            n <- toName n'
            t' <- helper (n ∷ accu) y'
            t'' <- helper accu y''
            return $ ρ t ∶ t' - t''
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "∀_space__string__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ ∀-A (fromList n) t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "Π_space__string__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ Π (fromList n) t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "ι_space__string__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ ι (fromList n) t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "λ_space__string__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ λ-A (fromList n) t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "Λ_space__string__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ Λ (fromList n) t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "{_space'__term__space'_,_space'__term__space__string__space'_._space'__term__space'_}") ,
          (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ _ ∷ y' ∷ _ ∷ n' ∷ _ ∷ _ ∷ y'' ∷ _ ∷ []) -> do
            t <- helper accu y
            t' <- helper accu y'
            n <- toName n'
            t'' <- helper (n ∷ accu) y''
            return [ t , t' ∙ t'' ]
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "φ_space__term__space__term__space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) -> do
            t <- helper accu y
            t' <- helper accu y'
            t'' <- helper accu y''
            return $ φ t t' t''
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "=_space__term__space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ []) -> do
            t <- helper accu y
            t' <- helper accu y'
            return $ t ≃ t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "ω_space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ []) -> do
            t <- helper accu y
            return $ M-A t
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "μ_space__term__space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ y' ∷ []) -> do
            t <- helper accu y
            t' <- helper accu y'
            return $ μ t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "ε_space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ []) -> do
            t <- helper accu y
            return $ ε t
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "Α_space__term_") , (case x₁ of λ -- alpha
          { (_ ∷ z ∷ []) -> do
            t <- helper accu z
            return $ Ev-A EvalStmt t
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "Β_space__term__space__term_") , (case x₁ of λ -- beta
          { (_ ∷ z ∷ _ ∷ z' ∷ []) -> do
            t <- helper accu z
            t' <- helper accu z'
            return $ Ev-A ShellCmd (t , t')
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "Γ_space__term__space__term_") , (case x₁ of λ
          { (_ ∷ z ∷ _ ∷ z' ∷ []) -> do
            t <- helper accu z
            t' <- helper accu z'
            return $ Ev-A CatchErr (t , t')
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "Δ_space__term__space__term_") , (case x₁ of λ
          { (_ ∷ z ∷ _ ∷ z' ∷ []) -> do
            t <- helper accu z
            t' <- helper accu z'
            return $ Ev-A CheckTerm (t , t')
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "Κ_const_") , (case x₁ of λ
          { (z ∷ []) -> do
            c <- toConst z
            return $ Const-A c
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "κ_char_") , (case x₁ of λ
          { (z ∷ []) -> do
            c <- addMaybe (toChar z) (toChar' z)
            return (Char-A c)
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term" "γ_space__term__space__term_") , (case x₁ of λ
          { (_ ∷ z ∷ _ ∷ z' ∷ []) -> do
            t <- helper accu z
            t' <- helper accu z'
            return (CharEq-A t t')
          ; _ -> nothing })) ∷

        []
        default nothing

data Stmt : Set where
  Let : GlobalName -> AnnTerm -> Maybe AnnTerm -> Stmt
  Ass : GlobalName -> AnnTerm -> Stmt
  Normalize : AnnTerm -> Stmt
  HeadNormalize : AnnTerm -> Stmt
  EraseSt : AnnTerm -> Stmt
  Test : AnnTerm -> Stmt
  SetEval : AnnTerm -> String -> String -> Stmt
  Import : String -> Stmt
  Shell : String -> Stmt
  Empty : Stmt

instance
  Stmt-Show : Show Stmt
  Stmt-Show = record { show = helper }
    where
      helper : Stmt -> String
      helper (Let x x₁ (just x₂)) = "let " + show {{CharList-Show}} x + " := " + show x₁ + " : " + show x₂
      helper (Let x x₁ nothing) = "let " + show {{CharList-Show}} x + " := " + show x₁
      helper (Ass x x₁) = "ass " + show {{CharList-Show}} x + " : " + show x₁
      helper (Normalize x) = "normalize " + show x
      helper (HeadNormalize x) = "normalize " + show x
      helper (EraseSt x) = "erase " + show x
      helper (Test x) = "test " + show x
      helper (SetEval x n n') = "seteval " + show x + " " + n + " " + n'
      helper (Import s) = "import " + s
      helper (Shell x) = "shell \"" + show x + "\""
      helper Empty = "Empty"

toStmt : Tree (ℕ ⊎ Char) -> Maybe Stmt
toStmt (Node x (_ ∷ (Node x' x₂) ∷ [])) =
  if (x ≣ (from-just $ ruleId "stmt" "_space'__stmt'_"))
    then
      decCase x' of
        ((from-just $ ruleId "stmt'" "let_space__string__space'_:=_space'__term__space'__lettail_") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) → do
              n <- toName y
              t <- toTerm y'
              return (Let n t (toLetTail y''))
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'"
          "ass_space__string__space'_:_space'__term__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ _ ∷ y₁ ∷ _ ∷ []) -> do
              n <- toName y
              t <- toTerm y₁
              return (Ass n t)
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "normalize_space__term__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) -> do
              t <- toTerm y
              return (Normalize t)
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "hnf_space__term__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) -> do
              t <- toTerm y
              return (HeadNormalize t)
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "erase_space__term__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) -> do
              t <- toTerm y
              return (EraseSt t)
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "test_space__term__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) -> do
              t <- toTerm y
              return (Test t)
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "seteval_space__term__space__string__space__string__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ y'' ∷ _ ∷ []) -> do
              t <- toTerm y
              n <- toName y'
              n' <- toName y''
              return (SetEval t (fromList n) (fromList n'))
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "import_space__string__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) -> do
              n <- toName y
              return $ Import (fromList n)
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "cmd_space__string__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) -> do
              n <- toName y
              return (Shell $ fromList n)
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "") ,
          return Empty) ∷

        []
      default nothing
    else nothing

  where
    toLetTail : Tree (ℕ ⊎ Char) -> Maybe AnnTerm
    toLetTail (Node x x₁) =
      decCase x of
        ((from-just $ ruleId "lettail" ":_space'__term__space'_.") ,
          (case x₁ of λ
            { (_ ∷ y ∷ _ ∷ []) -> toTerm y
            ; _ -> nothing })) ∷
        []
      default nothing

{-# CATCHALL #-}
toStmt _ = nothing

module CoreParser-Internal {M} {{_ : Monad M}} {{_ : MonadExcept M String}} where

  preCoreGrammar : M Grammar
  preCoreGrammar = generateCFG "stmt" coreGrammarGenerator

  parse' : Grammar -> String -> M (Tree (List Char ⊎ Char) × String)
  parse' (fst , fst₁ , snd) s = do
    res <- LL1Parser.parse (fromList ∘ proj₂ snd) matchMulti show fst₁ M s
    return (Data.Product.map₁ (fmap {{Tree-Functor}} (Data.Sum.map₁ (proj₁ snd))) res)

  parse : String -> M (Tree (List Char ⊎ Char) × String)
  parse s = do
    G <- preCoreGrammar
    parse' G s

  {-# TERMINATING #-} -- cannot just use sequence here because of the char special case
  synTreeToℕTree : Tree (List Char ⊎ Char) -> M (Tree (ℕ ⊎ Char))
  synTreeToℕTree t@(Node (inj₁ x) x₁) = do
    case convertIfChar t of λ
      { (just t') → return t'
      ; nothing → do
        id <- fullRuleId x
        ids <- sequence $ map synTreeToℕTree x₁
        return (Node id ids)
      }
    where
      fullRuleId : List Char -> M (ℕ ⊎ Char)
      fullRuleId l with break (_≟ '$') l -- split at '$'
      ... | (x , []) = throwError "No '$' character found!"
      ... | (x , _ ∷ y) = maybeToError (ruleId x y) ("Rule " + (fromList l) + "doesn't exist!")

      convertIfChar : Tree (List Char ⊎ Char) -> Maybe (Tree (ℕ ⊎ Char))
      convertIfChar (Node (inj₁ x) x₁) =
        addMaybe
          (join $ continueIfInit "nameInitChar$" x λ { [] → nothing ; (c ∷ x) → just $ Node (inj₂ $ unescape c x) [] }) $
          join $ continueIfInit "nameTailChar$" x λ { [] → nothing ; (c ∷ x) → just $ Node (inj₂ $ unescape c x) [] }
      convertIfChar (Node (inj₂ x) x₁) = nothing

  synTreeToℕTree (Node (inj₂ x) x₁) = return (Node (inj₂ x) [])

  parseStmt : String -> M (Stmt × String)
  parseStmt s = do
    (y' , rest) <- parse s
    y <- synTreeToℕTree y'
    case toStmt y of λ
      { (just x) → return (x , rest)
      ; nothing →
        throwError ("Error while converting syntax tree to statement!\nTree:\n" + show y + "\nRemaining: " + s) }

open CoreParser-Internal public
