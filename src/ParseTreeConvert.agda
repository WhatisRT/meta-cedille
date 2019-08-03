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

ruleId : List Char -> List Char -> Maybe ℕ
ruleId nonterm rule = do
  rules <- lookup nonterm parseRuleMap
  findIndexList (_≟ (nonterm + "$" + rule)) rules

toSort : Tree ℕ -> Maybe Sort
toSort (Node x x₁) = do
  if x ≣ (from-just $ ruleId "sort" "*")
    then return ⋆
    else (if x ≣ (from-just $ ruleId "sort" "□")
      then return □
      else nothing)

toName : Tree ℕ -> Maybe (List Char)
toName (Node x x₁) = case x₁ of λ
  { (y ∷ y' ∷ _) -> do
    c <- toChar y
    n <- toName' y'
    return (c ∷ n)
  ; _ -> nothing }
  where
    treeToWord32 : Tree ℕ -> Maybe Word32
    treeToWord32 (Node x (x0 ∷ x1 ∷ x2 ∷ x3 ∷ [])) = do
      y0 <- treeToByte x0
      y1 <- treeToByte x1
      y2 <- treeToByte x2
      y3 <- treeToByte x3
      return (mkWord32 y0 y1 y2 y3)
      where
        treeToByte : Tree ℕ -> Maybe Byte
        treeToByte (Node x (
          (Node x0 _) ∷ (Node x1 _) ∷ (Node x2 _) ∷ (Node x3 _) ∷
          (Node x4 _) ∷ (Node x5 _) ∷ (Node x6 _) ∷ (Node x7 _) ∷ []))
          = do
          y0 <- ℕtoBit x0
          y1 <- ℕtoBit x1
          y2 <- ℕtoBit x2
          y3 <- ℕtoBit x3
          y4 <- ℕtoBit x4
          y5 <- ℕtoBit x5
          y6 <- ℕtoBit x6
          y7 <- ℕtoBit x7
          return (mkByte y0 y1 y2 y3 y4 y5 y6 y7)
          where
            ℕtoBit : ℕ -> Maybe Bool
            ℕtoBit zero = return false
            ℕtoBit (suc zero) = return true
            ℕtoBit (suc (suc x)) = nothing
        {-# CATCHALL #-}
        treeToByte _ = nothing
    {-# CATCHALL #-}
    treeToWord32 _ = nothing

    toChar : Tree ℕ -> Maybe Char
    toChar = mmap bytesToChar ∘ treeToWord32

    toName' : Tree ℕ -> Maybe (List Char)
    toName' (Node x x₁) = case x₁ of λ
      { (y ∷ y' ∷ _) -> do
        c <- toChar y
        n <- toName' y'
        return (c ∷ n)
      ; [] -> (if x ≣ (from-just $ ruleId "name'" "")
          then return []
          else nothing)
      ; _ -> nothing }

toIndex : Tree ℕ -> Maybe ℕ
toIndex t = do
  res <- helper t
  foldl {A = Maybe ℕ} (λ x c → do
    x' <- x
    return $ 10 * x' + c) (just 0) res
  where
    helper' : Tree ℕ -> Maybe (List ℕ)
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

    helper : Tree ℕ -> Maybe (List ℕ)
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

toTerm : Tree ℕ -> Maybe AnnTerm
toTerm = helper []
  where
    helper : List (List Char) -> Tree ℕ -> Maybe AnnTerm
    helper accu (Node x x₁) =
      decCase x of
        ((from-just $ ruleId "term" "_var_") ,
          head x₁ >>=
            λ { (Node y (n ∷ [])) ->
                decCase y of
                  ((from-just $ ruleId "var" "_name_") , do
                    n' <- toName n
                    case findIndexList (n' ≟_) accu of (λ
                      { (just x) → return $ Var-A $ Bound $ fromℕ x
                      ; nothing → return $ Var-A $ Free (fromList n') })) ∷
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
          "ρ_space__term__space__name__space'_._space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ _ ∷ n' ∷ _ ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) -> do
            t <- helper accu y
            n <- toName n'
            t' <- helper (n ∷ accu) y'
            t'' <- helper accu y''
            return $ ρ t ∶ t' - t''
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "∀_space__name__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ ∀-A t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "Π_space__name__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ Π t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "ι_space__name__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ ι t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "λ_space__name__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ λ-A t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "Λ_space__name__space'_:_space'__term__space__term_") , (case x₁ of λ
          { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
            n <- toName n'
            t <- helper accu y
            t' <- helper (n ∷ accu) y'
            return $ Λ t t'
          ; _ -> nothing })) ∷

        ((from-just $ ruleId "term"
          "{_space'__term__space'_,_space'__term__space__name__space'_._space'__term__space'_}") ,
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

        ((from-just $ ruleId "term" "ζ_space__term_") , (case x₁ of λ
          { (_ ∷ y ∷ []) -> do
            t <- helper accu y
            return $ Ev-A t
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
      helper (Let x x₁ (just x₂)) = "let " + show x + " := " + show x₁ + " : " + show x₂
      helper (Let x x₁ nothing) = "let " + show x + " := " + show x₁
      helper (Ass x x₁) = "ass " + show x + " : " + show x₁
      helper (Normalize x) = "normalize " + show x
      helper (HeadNormalize x) = "normalize " + show x
      helper (EraseSt x) = "erase " + show x
      helper (Test x) = "test " + show x
      helper (SetEval x n n') = "seteval " + show x + " " + n + " " + n'
      helper (Import s) = "import " + s
      helper (Shell x) = "shell \"" + show x + "\""
      helper Empty = "Empty"

toStmt : Tree ℕ -> Maybe Stmt
toStmt (Node x (_ ∷ (Node x' x₂) ∷ [])) =
  if (x ≣ (from-just $ ruleId "stmt" "_space'__stmt'_"))
    then
      decCase x' of
        ((from-just $ ruleId "stmt'" "let_space__name__space'_:=_space'__term__space'__lettail_") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) → do
              n <- toName y
              t <- toTerm y'
              return (Let (Global (fromList n)) t (toLetTail y''))
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'"
          "ass_space__name__space'_:_space'__term__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ _ ∷ y₁ ∷ _ ∷ []) -> do
              n <- toName y
              t <- toTerm y₁
              return (Ass (Global (fromList n)) t)
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

        ((from-just $ ruleId "stmt'" "seteval_space__term__space__name__space__name__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ y'' ∷ _ ∷ []) -> do
              t <- toTerm y
              n <- toName y'
              n' <- toName y''
              return (SetEval t (fromList n) (fromList n'))
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "import_space__name__space'_.") ,
          (case x₂ of λ
            { (_ ∷ y ∷ _ ∷ []) -> do
              n <- toName y
              return $ Import (fromList n)
            ; _ -> nothing })) ∷

        ((from-just $ ruleId "stmt'" "cmd_space__name__space'_.") ,
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
    toLetTail : Tree ℕ -> Maybe AnnTerm
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

  synTreeHasNoMultiChar : Tree (List Char ⊎ Char) -> M (Tree (List Char))
  synTreeHasNoMultiChar t = sequence $ fmap {{Tree-Functor}} (λ
    { (inj₁ x) → return x
    ; (inj₂ y) → throwError "Tree had a multi char"}) t

  {-# TERMINATING #-} -- cannot just use sequence here because of the char special case
  synTreeToℕTree : Tree (List Char) -> M (Tree ℕ)
  synTreeToℕTree t@(Node x x₁) =
    case convertIfChar t of λ
      { (just t') → return t'
      ; nothing → do
        id <- fullRuleId x
        ids <- sequence $ map synTreeToℕTree x₁
        return (Node id ids)
      }
    where
      fullRuleId : List Char -> M ℕ
      fullRuleId l with break (_≟ '$') l -- split at '$'
      ... | (x , []) = throwError "No '$' character found!"
      ... | (x , _ ∷ y) = maybeToError (ruleId x y) ("Rule " + (fromList l) + "doesn't exist!")

      charToℕTree : Char -> Tree ℕ
      charToℕTree c with charToWord32 c
      ... | mkWord32 x1 x2 x3 x4 =
        Node 0 ((byteToℕTree x1) ∷ (byteToℕTree x2) ∷ (byteToℕTree x3) ∷ (byteToℕTree x4) ∷ [])
        where
          bitToℕTree : Bool -> Tree ℕ
          bitToℕTree false = Node 0 []
          bitToℕTree true = Node 1 []

          byteToℕTree : Byte -> Tree ℕ
          byteToℕTree (mkByte x1 x2 x3 x4 x5 x6 x7 x8) =
            Node 0 ((bitToℕTree x1) ∷ (bitToℕTree x2) ∷ (bitToℕTree x3) ∷ (bitToℕTree x4) ∷
                    (bitToℕTree x5) ∷ (bitToℕTree x6) ∷ (bitToℕTree x7) ∷ (bitToℕTree x8) ∷ [])

      convertIfChar : Tree (List Char) -> Maybe (Tree ℕ)
      convertIfChar (Node x x₁) =
        addMaybe
          (join $ continueIfInit "nameInitChar$" x λ { [] → nothing ; (c ∷ x) → just $ charToℕTree (unescape c x) }) $
          join $ continueIfInit "nameTailChar$" x λ { [] → nothing ; (c ∷ x) → just $ charToℕTree (unescape c x) }

  parseStmt : String -> M (Stmt × String)
  parseStmt s = do
    (y' , rest) <- parse s
    y'' <- synTreeHasNoMultiChar y'
    y <- synTreeToℕTree y''
    case toStmt y of λ
      { (just x) → return (x , rest)
      ; nothing →
        throwError ("Error while converting syntax tree to statement: "
          + show {{Tree-Show {{CharList-Show}}}} y'') }

open CoreParser-Internal public
