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
open import Data.List using (uncons)

open import CoreTheory
open import Parse.TreeConvert using (toTerm; toName; toNameList)

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
    extractConstrId (Var-P (Free x)) = throwError ("Not a constructor:" <+> x)
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
                         ("\nError while converting term" <+> show t
                         <+> "to a tree of constructors of a" <+> nameOfA <+> "!")
      maybeToError (conversionFunction t') ("Error while converting to" <+> nameOfA + ". Term:"
                                           <+> show t + "\nTree:\n" + show {{Tree-Show}} t')

  open Unquote {{...}} public

  instance
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

  private
    Quotable-Index : Quotable 𝕀
    Quotable-Index .quoteToAnnTerm i with uncons (toList (show i))
    ... | nothing      = Sort-A □ -- impossible
    ... | just (x , i) = FreeVar ("init$index$" + fromList [ x ] + "_index'_") ⟪$⟫ quoteIndex' i
      where
        quoteIndex' : List Char → AnnTerm
        quoteIndex' [] = FreeVar "init$index'$"
        quoteIndex' (x ∷ xs) = FreeVar ("init$index'$" + fromList [ x ] + "_index'_") ⟪$⟫ quoteIndex' xs

  Quotable-AnnTerm : Quotable AnnTerm
  Quotable-AnnTerm .quoteToAnnTerm (Var-A (Bound x)) = FreeVar "init$term$_var_"
    ⟪$⟫ (FreeVar "init$var$_index_" ⟪$⟫ quoteToAnnTerm x)
  Quotable-AnnTerm .quoteToAnnTerm (Var-A (Free x)) = FreeVar "init$term$_var_"
    ⟪$⟫ (FreeVar "init$var$_string_" ⟪$⟫ quoteToAnnTerm x)
  Quotable-AnnTerm .quoteToAnnTerm (Sort-A ⋆) = FreeVar "init$term$_sort_" ⟪$⟫ FreeVar "init$sort$=ast="
  Quotable-AnnTerm .quoteToAnnTerm (Sort-A □) = FreeVar "init$term$_sort_" ⟪$⟫ FreeVar "init$sort$=sq="
  Quotable-AnnTerm .quoteToAnnTerm (Const-A CharT) =
    FreeVar "init$term$=Kappa=_const_" ⟪$⟫ FreeVar "init$const$Char"
  Quotable-AnnTerm .quoteToAnnTerm (Pr1-A t) = FreeVar "init$term$=pi=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (Pr2-A t) = FreeVar "init$term$=psi=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (Beta-A t t₁) =
    FreeVar "init$term$=beta=^space^_term_^space^_term_" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Delta-A t t₁) =
    FreeVar "init$term$=delta=^space^_term_^space^_term_" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Sigma-A t) = FreeVar "init$term$=sigma=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (App-A t t₁) =
    FreeVar "init$term$=lsquare=^space'^_term_^space^_term_^space'^=rsquare="
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (AppE-A t t₁) =
    FreeVar "init$term$=langle=^space'^_term_^space^_term_^space'^=rangle="
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Rho-A t t₁ t₂) =
    FreeVar "init$term$=rho=^space^_term_^space^_string_^space'^=dot=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm (List Char ∋ "_") -- TODO: add a name to rho?
      ⟪$⟫ quoteToAnnTerm t₁ ⟪$⟫ quoteToAnnTerm t₂
  Quotable-AnnTerm .quoteToAnnTerm (All-A x t t₁) =
    FreeVar "init$term$=forall=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Pi-A x t t₁) =
    FreeVar "init$term$=Pi=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Iota-A x t t₁) =
    FreeVar "init$term$=iota=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Lam-A x t t₁) =
    FreeVar "init$term$=lambda=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (LamE-A x t t₁) =
    FreeVar "init$term$=Lambda=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Pair-A t t₁ t₂) =
    FreeVar "init$term$=lbrace=^space'^_term_^space'^=comma=^space'^_term_^space^_string_^space'^=dot=^space'^_term_^space'^=rbrace=" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
      ⟪$⟫ quoteToAnnTerm (List Char ∋ "_") ⟪$⟫ quoteToAnnTerm t₂ -- TODO: add a name to pair?
  Quotable-AnnTerm .quoteToAnnTerm (Phi-A t t₁ t₂) =
    FreeVar "init$term$=phi=^space^_term_^space^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁ ⟪$⟫ quoteToAnnTerm t₂
  Quotable-AnnTerm .quoteToAnnTerm (Eq-A t t₁) =
    FreeVar "init$term$=equal=^space^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (M-A t) = FreeVar "init$term$=omega=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (Mu-A t t₁) =
    FreeVar "init$term$=mu=^space^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Epsilon-A t) =
    FreeVar "init$term$=epsilon=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (Gamma-A t t₁) =
    FreeVar "init$term$=zeta=CatchErr^space^_term_^space^_term_" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Ev-A x x₁) = Sort-A □ -- TODO
  Quotable-AnnTerm .quoteToAnnTerm (Char-A x) = FreeVar "init$term$=kappa=_char_" ⟪$⟫ Char-A x
  Quotable-AnnTerm .quoteToAnnTerm (CharEq-A t t₁) =
    FreeVar "init$term$=gamma=^space^_term_^space^_term_" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁

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
