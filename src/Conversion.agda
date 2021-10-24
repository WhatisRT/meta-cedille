--------------------------------------------------------------------------------
-- This file contains functions to convert between agda terms and meta-cedille
-- terms
--------------------------------------------------------------------------------

module Conversion where

open import Class.Monad.Except
open import Data.String using (fromList; toList)
open import Data.Tree
open import Data.Tree.Instance
open import Data.Word using (toℕ)

open import CoreTheory
open import Parse.TreeConvert

open import Prelude
open import Prelude.Strings

module _ {M : Set → Set} {{_ : Monad M}} {{_ : MonadExcept M String}} where
  private
    {-# TERMINATING #-} -- findOutermostConstructor returns a list of smaller terms
    buildConstructorTree : Context → PureTerm → Tree PureTerm
    buildConstructorTree Γ t with findOutermostConstructor t
    ... | t' , ts = Node t' $ map (buildConstructorTree Γ) $ reverse ts

    extractConstrId : PureTerm → M (ℕ ⊎ Char)
    extractConstrId (Var-P (Bound x)) = return $ inj₁ $ toℕ x
    extractConstrId (Var-P (Free x)) = throwError "Not a constructor"
    extractConstrId (Char-P c) = return $ inj₂ c
    {-# CATCHALL #-}
    extractConstrId t = throwError ("Not a variable" <+> show t)

    {-# TERMINATING #-}
    extractConstrIdTree : Tree PureTerm → M (Tree (ℕ ⊎ Char))
    extractConstrIdTree (Node x y) = do
      x' ← extractConstrId x
      y' ← sequence (map extractConstrIdTree y)
      return $ Node x' y'

  record Unquote (A : Set) : Set where
    field
      conversionFunction : Tree (ℕ ⊎ Char) → Maybe A
      nameOfA            : String

    unquoteConstrs : Context → PureTerm → M A
    unquoteConstrs Γ t = do
      t' ← appendIfError (extractConstrIdTree $ buildConstructorTree Γ t)
                         ("Error while converting term" <+> show t
                         <+> "to a tree of constructors of a" <+> nameOfA <+> "!")
      maybeToError (conversionFunction t') ("Error while converting to" <+> nameOfA + ". Term:"
                                           <+> show t + "\nTree:\n" + show {{Tree-Show}} t')

  open Unquote {{...}} public

  instance
    Unquote-Stmt : Unquote Stmt
    Unquote-Stmt = record { conversionFunction = toStmt ; nameOfA = "statement" }

    Unquote-Term : Unquote AnnTerm
    Unquote-Term = record { conversionFunction = toTerm ; nameOfA = "term" }

    Unquote-String : Unquote String
    Unquote-String = record { conversionFunction = toName ; nameOfA = "string" }

    Unquote-StringList : Unquote (List String)
    Unquote-StringList = record { conversionFunction = toNameList ; nameOfA = "string list" }

record Quotable (A : Set) : Set₁ where
  field
    quoteToAnnTerm : A → AnnTerm

  quoteToPureTerm : A → PureTerm
  quoteToPureTerm = Erase ∘ quoteToAnnTerm

open Quotable {{...}} public

instance
  Quotable-ListChar : Quotable (List Char)
  Quotable-ListChar .quoteToAnnTerm [] = FreeVar "init$string$nil"
  Quotable-ListChar .quoteToAnnTerm (c ∷ cs) = FreeVar "init$string$cons" ⟪$⟫ Char-A c ⟪$⟫ quoteToAnnTerm cs

  Quotable-String : Quotable String
  Quotable-String .quoteToAnnTerm = quoteToAnnTerm ∘ toList

  Quotable-ListString : Quotable (List String)
  Quotable-ListString .quoteToAnnTerm [] = FreeVar "init$stringList$nil"
  Quotable-ListString .quoteToAnnTerm (x ∷ l) =
    FreeVar "init$stringList$cons" ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm l

  Quotable-AnnTerm : Quotable AnnTerm
  Quotable-AnnTerm .quoteToAnnTerm t = Sort-A □ -- TODO

  Quotable-PureTerm : Quotable PureTerm
  Quotable-PureTerm .quoteToAnnTerm t = Sort-A □ -- TODO

  Quotable-ListTerm : Quotable (List AnnTerm)
  Quotable-ListTerm .quoteToAnnTerm [] = FreeVar "init$termList$nil"
  Quotable-ListTerm .quoteToAnnTerm (x ∷ l) = FreeVar "init$termList$cons" ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm l

Quotable-NoQuoteAnnTerm : Quotable AnnTerm
Quotable-NoQuoteAnnTerm .quoteToAnnTerm t = t

record ProductData (L R : Set) : Set where
  field
    lType rType : AnnTerm
    l : L
    r : R

-- The type of results of executing a statement in the interpreter. This can be
-- returned back to the code via embedExecutionResult
MetaResult = List String × List AnnTerm

instance
  Quotable-MetaResult : Quotable MetaResult
  Quotable-MetaResult .quoteToAnnTerm (fst , snd) =
    FreeVar "init$metaResult$pair" ⟪$⟫ quoteToAnnTerm fst ⟪$⟫ quoteToAnnTerm snd

  Quotable-ProductData : ∀ {L R} ⦃ _ : Quotable L ⦄ ⦃ _ : Quotable R ⦄ → Quotable (ProductData L R)
  Quotable-ProductData .quoteToAnnTerm pDat = let open ProductData pDat in
    FreeVar "init$pair" ⟪$⟫ lType ⟪$⟫ rType ⟪$⟫ quoteToAnnTerm l ⟪$⟫ quoteToAnnTerm r
