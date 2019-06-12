--------------------------------------------------------------------------------
-- This file contains functions to turn the tree of parse results into the agda
-- data structures they represent.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module ParseTreeConvert where

import Data.Product
open import Agda.Builtin.Nat using (_-_)
open import Class.Monad.Except
open import Class.Traversable
open import Data.Char using (toNat)
open import Data.Fin.Instance
open import Data.List
open import Data.Maybe using () renaming (_<∣>_ to addMaybe)
open import Data.String using (fromList)
open import Data.Tree
open import Data.Tree.Instance
open import Relation.Nullary

open import Prelude
open import Prelude.Strings

open import CoreTheory
open import InitEnv
open import Parser
open import ParserGenerator

continueIfInit : ∀ {a} {A : Set a} -> List Char -> List Char -> (List Char -> A) -> Maybe A
continueIfInit {A = A} init s = helper init s
  where
    helper : List Char -> List Char -> (List Char -> A) -> Maybe A
    helper [] s f = just $ f s
    helper (x₁ ∷ init) [] f = nothing
    helper (x₁ ∷ init) (x ∷ s) f with x ≟ x₁
    ... | yes p = helper init s f
    ... | no ¬p = nothing

toSort : Tree (List Char) -> Maybe Sort
toSort (Node x x₁) = join $ continueIfInit "sort$" x (λ rest →
  if rest ≣ "*"
    then return ⋆
    else (if rest ≣ "□"
      then return □
      else nothing))

toName : Tree (List Char) -> Maybe (List Char)
toName (Node x x₁) = case x₁ of λ
  { (y ∷ y' ∷ _) -> do
    c <- toChar y
    n <- toName y'
    return (c ∷ n)
  ; [] -> addMaybe (join $ continueIfInit "name$" x λ { [] -> return [] ; _ -> nothing }) $
    join $ continueIfInit "name'$" x λ { [] -> return [] ; _ -> nothing }
  ; _ -> nothing }
  where
    toChar : Tree (List Char) -> Maybe Char
    toChar (Node c c₁) =
      addMaybe (join $ continueIfInit "nameInitChar$" c λ
        { [] → nothing ; (c' ∷ r) → just (unescape c' r) }) $
      addMaybe (join $ continueIfInit "nameTailChar$" c λ
        { [] → nothing ; (c' ∷ r) → just (unescape c' r) }) $
      join $ continueIfInit "char$" c λ
        { [] → nothing ; (c' ∷ r) → just (unescape c' r) }

toIndex : Tree (List Char) -> Maybe ℕ
toIndex t = do
  res <- helper t
  foldl {A = Maybe ℕ} (λ x c → do
    x' <- x
    c' <- charToDigit c
    return $ 10 * x' + c') (just 0) res
  where
    helper : Tree (List Char) -> Maybe (List Char)
    helper (Node x x₁) = addMaybe (join $ continueIfInit "index$" x λ
      { [] → nothing
      ; (x ∷ r) → case x₁ of λ { (t ∷ _) -> helper t >>= (return ∘ (x ∷_)) ; _ -> nothing } }) $
      join $ continueIfInit "index'$" x λ
        { [] → return []
        ; (x ∷ r) → case x₁ of λ { (t ∷ _) -> helper t >>= (return ∘ (x ∷_)) ; _ -> nothing } }

    charToDigit : Char -> Maybe ℕ
    charToDigit c with toNat c
    ... | n = if ⌊ 47 <? n ⌋ ∧ ⌊ n <? 58 ⌋ then just (n - 48) else nothing

toTerm : Tree (List Char) -> Maybe AnnTerm
toTerm = helper []
  where
    helper : List (List Char) -> Tree (List Char) -> Maybe AnnTerm
    helper accu (Node x x₁) = join $ continueIfInit "term$" x λ rest ->
      addMaybe (join $ continueIfInit "(" rest (λ _ -> case x₁ of λ
        { (y ∷ []) -> helper accu y ; _ -> nothing })) $

      addMaybe (join $ continueIfInit "_var_" rest λ _ ->
        maybe (λ { (Node y (n ∷ [])) ->
          maybe (λ t ->
            addMaybe
              (join $ continueIfInit "var$_name_" y λ _ -> do
                n' <- toName n
                case findIndexList (n' ≟_) accu of (λ
                  { (just x) → return $ Var-A $ Bound x
                  ; nothing → return $ Var-A $ Free (fromList n') }))
              (join $ continueIfInit "var$_index_" y λ _ -> do
                n' <- toIndex n
                return $ Var-A $ Bound n')
                ) nothing (head x₁) ; _ -> nothing }) nothing (head x₁)) $

      addMaybe (join $ continueIfInit "_sort_" rest λ _ -> case x₁ of λ
        { (y ∷ []) -> toSort y >>= λ y' -> return (Sort-A y') ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "π" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ []) -> do
          y' <- helper accu y
          return (y' ∙1)
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "ψ" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ []) -> do
          y' <- helper accu y
          return (y' ∙2)
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "β" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ y' ∷ []) -> do
          t <- helper accu y
          t' <- helper accu y'
          return $ β t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "δ" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ y' ∷ []) -> do
          t <- helper accu y
          t' <- helper accu y'
          return $ δ t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "σ" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ []) -> helper accu y >>= λ y' -> return (ς y') ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "[" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ []) -> do
          t <- helper accu y
          t' <- helper accu y'
          return $ App-A t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "<" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ []) -> do
          t <- helper accu y
          t' <- helper accu y'
          return $ AppE-A t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "ρ" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ n' ∷ _ ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) -> do
          t <- helper accu y
          n <- toName n'
          t' <- helper (n ∷ accu) y'
          t'' <- helper accu y''
          return $ ρ t ∶ t' - t''
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "∀" rest λ _ -> case x₁ of λ
        { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
          n <- toName n'
          t <- helper accu y
          t' <- helper (n ∷ accu) y'
          return $ ∀-A t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "Π" rest λ _ -> case x₁ of λ
        { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
          n <- toName n'
          t <- helper accu y
          t' <- helper (n ∷ accu) y'
          return $ Π t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "ι" rest λ _ -> case x₁ of λ
        { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
          n <- toName n'
          t <- helper accu y
          t' <- helper (n ∷ accu) y'
          return $ ι t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "λ" rest λ _ -> case x₁ of λ
        { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
          n <- toName n'
          t <- helper accu y
          t' <- helper (n ∷ accu) y'
          return $ λ-A t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "Λ" rest λ _ -> case x₁ of λ
        { (_ ∷ n' ∷ _ ∷ _ ∷ y ∷ _ ∷ y' ∷ []) -> do
          n <- toName n'
          t <- helper accu y
          t' <- helper (n ∷ accu) y'
          return $ Λ t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "{" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ _ ∷ y' ∷ _ ∷ n' ∷ _ ∷ _ ∷ y'' ∷ _ ∷ []) -> do
          t <- helper accu y
          t' <- helper accu y'
          n <- toName n'
          t'' <- helper (n ∷ accu) y''
          return [ t , t' ∙ t'' ]
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "φ" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) -> do
          t <- helper accu y
          t' <- helper accu y'
          t'' <- helper accu y''
          return $ φ t t' t''
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "=" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ y' ∷ []) -> do
          t <- helper accu y
          t' <- helper accu y'
          return $ t ≃ t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "ω" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ []) -> do
          t <- helper accu y
          return $ M-A t
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "μ" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ _ ∷ y' ∷ []) -> do
          t <- helper accu y
          t' <- helper accu y'
          return $ μ t t'
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "ε" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ []) -> do
          t <- helper accu y
          return $ ε t
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "ζ" rest λ _ -> case x₁ of λ
        { (_ ∷ y ∷ []) -> do
          t <- helper accu y
          return $ Ev-A t
        ; _ -> nothing }) $

      nothing

data Stmt : Set where
  Let : GlobalName -> AnnTerm -> Maybe AnnTerm -> Stmt
  Ass : GlobalName -> AnnTerm -> Stmt
  Normalize : AnnTerm -> Stmt
  HeadNormalize : AnnTerm -> Stmt
  EraseSt : AnnTerm -> Stmt
  Test : AnnTerm -> Stmt
  SetEval : AnnTerm -> String -> String -> Stmt
  Import : String -> Stmt
  Shell : AnnTerm -> Stmt
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

toStmt : Tree (List Char) -> Maybe Stmt
toStmt (Node x x₁) = join $ continueIfInit "stmt$" x λ _ -> case x₁ of λ
  { (_ ∷ (Node x' x₂) ∷ []) ->
    join $ continueIfInit "stmt'$" x' λ rest ->
      addMaybe (join $ continueIfInit "let" rest (λ _ -> case x₂ of λ
        { (y ∷ []) → toLet y
        ; _ -> nothing })) $

      addMaybe (join $ continueIfInit "ass" rest λ _ -> case x₂ of λ
        { (_ ∷ y ∷ _ ∷ _ ∷ y₁ ∷ _ ∷ []) -> do
          n <- toName y
          t <- toTerm y₁
          return (Ass (Global (fromList n)) t)
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "normalize" rest λ _ -> case x₂ of λ
        { (_ ∷ y ∷ _ ∷ []) -> do
          t <- toTerm y
          return (Normalize t)
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "hnf" rest λ _ -> case x₂ of λ
        { (_ ∷ y ∷ _ ∷ []) -> do
          t <- toTerm y
          return (HeadNormalize t)
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "erase" rest λ _ -> case x₂ of λ
        { (_ ∷ y ∷ _ ∷ []) -> do
          t <- toTerm y
          return (EraseSt t)
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "test" rest λ _ -> case x₂ of λ
        { (_ ∷ y ∷ _ ∷ []) -> do
          t <- toTerm y
          return (Test t)
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "seteval" rest λ _ -> case x₂ of λ
        { (_ ∷ y ∷ _ ∷ y' ∷ _ ∷ y'' ∷ _ ∷ []) -> do
          t <- toTerm y
          n <- toName y'
          n' <- toName y''
          return (SetEval t (fromList n) (fromList n'))
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "import" rest λ _ -> case x₂ of λ
        { (_ ∷ y ∷ _ ∷ []) -> do
          n <- toName y
          return $ Import (fromList n)
        ; _ -> nothing }) $

      addMaybe (join $ continueIfInit "cmd" rest λ _ -> case x₂ of λ
        { (_ ∷ y ∷ _ ∷ []) -> do
          t <- toTerm y
          return (Shell t)
        ; _ -> nothing }) $

      if rest ≣ "" then return Empty else nothing
  ; _ -> nothing }
  where
    toLet : Tree (List Char) -> Maybe Stmt
    toLet (Node x x₁) = join $ continueIfInit "let$" x λ _ -> case x₁ of λ
      { (_ ∷ y ∷ _ ∷ _ ∷ y' ∷ _ ∷ y'' ∷ []) -> do
        n <- toName y
        t <- toTerm y'
        return $ Let (Global (fromList n)) t (toLetTail y'')
      ; _ -> nothing}
        where
          toLetTail : Tree (List Char) -> Maybe AnnTerm
          toLetTail (Node x x₁) = join $ continueIfInit "lettail$" x λ rest ->
            addMaybe (join $ continueIfInit "." rest λ _ -> nothing)
              (join $ continueIfInit ":" rest λ _ -> case x₁ of λ
                { (_ ∷ y ∷ _ ∷ []) -> toTerm y
                ; _ -> nothing })

coreGrammarGenerator : List (List Char)
coreGrammarGenerator = from-just $ sequence $ map translate grammarWithChars

module CoreParser-Internal {M} {{_ : Monad M}} {{_ : MonadExcept M String}} where

  preCoreGrammar : M Grammar
  preCoreGrammar = generateCFG "stmt" coreGrammarGenerator

  parse' : Grammar -> String -> M (Tree (List Char) × String)
  parse' (fst , fst₁ , snd) s = do
    res <- LL1Parser.parse fst₁ (fromList ∘ proj₂ snd) M s
    return (Data.Product.map (fmap {{Tree-Functor}} (proj₁ snd)) id res)

  parse : String -> M (Tree (List Char) × String)
  parse s = do
    G <- preCoreGrammar
    parse' G s

  parseStmt : String -> M (Stmt × String)
  parseStmt s = do
    (y , rest) <- parse s
    case toStmt y of λ
      { (just x) → return (x , rest)
      ; nothing →
        throwError ("Error while converting syntax tree to statement: "
          + (show {{Tree-Show {{Char-Show}}}} y)) }

open CoreParser-Internal public
