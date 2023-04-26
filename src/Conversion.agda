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

open import Theory.TypeChecking
open import Parse.TreeConvert using (toTerm; toName; toNameList)

open import Prelude
open import Prelude.Strings

module _ {M : Set → Set} {{_ : Monad M}} {{_ : MonadExcept M String}} where

  record Unquote (A : Set) : Set where
    field
      conversionFunction : Tree (ℕ ⊎ Char) → Maybe A
      nameOfA            : String

  open Unquote {{...}} public

  {-# TERMINATING #-}
  unquoteConstrs : {A : Set} ⦃ _ : Unquote A ⦄ → Context → PureTerm → M A
  unquoteConstrs Γ t = do
    t' ← appendIfError (extractConstrIdTree $ buildConstructorTree Γ t)
                       ("\nError while converting term" <+> show t
                       <+> "to a tree of constructors of a" <+> nameOfA <+> "!")
    maybeToError (conversionFunction t') ("Error while converting to" <+> nameOfA + ". Term:"
                                         <+> show t + "\nTree:\n" + show {{Tree-Show}} t')
    where
      findOutermostConstructor : PureTerm → PureTerm × List PureTerm
      findOutermostConstructor = outermostApp ∘ stripBinders
        where
          stripBinders : PureTerm → PureTerm
          stripBinders t with stripBinder t
          ... | just x = stripBinders x
          ... | nothing = t

          outermostApp : PureTerm → PureTerm × List PureTerm
          outermostApp (App t t₁) = map₂ (t₁ ∷_) $ outermostApp t
          {-# CATCHALL #-}
          outermostApp t = t , []

      buildConstructorTree : Context → PureTerm → Tree PureTerm
      buildConstructorTree Γ t with findOutermostConstructor t
      ... | t' , ts = Node t' $ map (buildConstructorTree Γ) $ reverse ts

      extractConstrId : PureTerm → M (ℕ ⊎ Char)
      extractConstrId (Var-T (Bound x)) = return $ inj₁ $ toℕ x
      extractConstrId (Var-T (Free x)) = throwError ("Not a constructor:" <+> x)
      extractConstrId (Char-T c) = return $ inj₂ c
      {-# CATCHALL #-}
      extractConstrId t = throwError ("Not a variable" <+> show t)

      extractConstrIdTree : Tree PureTerm → M (Tree (ℕ ⊎ Char))
      extractConstrIdTree (Node x y) = do
        x' ← extractConstrId x
        y' ← sequence (map extractConstrIdTree y)
        return $ Node x' y'

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
  Quotable-Unit : Quotable ⊤
  Quotable-Unit .quoteToAnnTerm _ = FreeVar "init$tt"

  Quotable-ListChar : Quotable (List Char)
  Quotable-ListChar .quoteToAnnTerm [] = FreeVar "stringNil"
  Quotable-ListChar .quoteToAnnTerm (c ∷ cs) = FreeVar "stringCons" ⟪$⟫ Char-T c ⟪$⟫ quoteToAnnTerm cs

  Quotable-String : Quotable String
  Quotable-String .quoteToAnnTerm = quoteToAnnTerm ∘ toList

  Quotable-ListString : Quotable (List String)
  Quotable-ListString .quoteToAnnTerm [] = FreeVar "init$stringList$nil"
  Quotable-ListString .quoteToAnnTerm (x ∷ l) =
    FreeVar "init$stringList$cons" ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm l

  private
    Quotable-Index : Quotable 𝕀
    Quotable-Index .quoteToAnnTerm i with uncons (toList (show i))
    ... | nothing      = □ -- impossible
    ... | just (x , i) = FreeVar ("init$index$" + fromList [ x ] + "_index'_") ⟪$⟫ quoteIndex' i
      where
        quoteIndex' : List Char → AnnTerm
        quoteIndex' [] = FreeVar "init$index'$"
        quoteIndex' (x ∷ xs) = FreeVar ("init$index'$" + fromList [ x ] + "_index'_") ⟪$⟫ quoteIndex' xs

  Quotable-AnnTerm : Quotable AnnTerm
  Quotable-AnnTerm .quoteToAnnTerm (Var-T (Bound x)) = FreeVar "init$term$_var_"
    ⟪$⟫ (FreeVar "init$var$_index_" ⟪$⟫ quoteToAnnTerm x)
  Quotable-AnnTerm .quoteToAnnTerm (Var-T (Free x)) = FreeVar "init$term$_var_"
    ⟪$⟫ (FreeVar "init$var$_string_" ⟪$⟫ quoteToAnnTerm x)
  Quotable-AnnTerm .quoteToAnnTerm (Sort-T Ast) = FreeVar "init$term$_sort_" ⟪$⟫ FreeVar "init$sort$=ast="
  Quotable-AnnTerm .quoteToAnnTerm (Sort-T Sq) = FreeVar "init$term$_sort_" ⟪$⟫ FreeVar "init$sort$=sq="
  Quotable-AnnTerm .quoteToAnnTerm (Const-T CharT) =
    FreeVar "init$term$=Kappa=_const_" ⟪$⟫ FreeVar "init$const$Char"
  Quotable-AnnTerm .quoteToAnnTerm (Pr1 t) = FreeVar "init$term$=pi=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (Pr2 t) = FreeVar "init$term$=psi=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (Beta t t₁) =
    FreeVar "init$term$=beta=^space^_term_^space^_term_" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Delta t t₁) =
    FreeVar "init$term$=delta=^space^_term_^space^_term_" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Sigma t) = FreeVar "init$term$=sigma=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (App t t₁) =
    FreeVar "init$term$=lsquare=^space'^_term_^space^_term_^space'^=rsquare="
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (AppE t t₁) =
    FreeVar "init$term$=langle=^space'^_term_^space^_term_^space'^=rangle="
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Rho t t₁ t₂) =
    FreeVar "init$term$=rho=^space^_term_^space^_string_^space'^=dot=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm (List Char ∋ "_") -- TODO: add a name to rho?
      ⟪$⟫ quoteToAnnTerm t₁ ⟪$⟫ quoteToAnnTerm t₂
  Quotable-AnnTerm .quoteToAnnTerm (All x t t₁) =
    FreeVar "init$term$=forall=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Pi x t t₁) =
    FreeVar "init$term$=Pi=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Iota x t t₁) =
    FreeVar "init$term$=iota=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Lam-A x t t₁) =
    FreeVar "init$term$=lambda=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (LamE x t t₁) =
    FreeVar "init$term$=Lambda=^space^_string_^space'^=colon=^space'^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm x ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Pair t t₁ t₂) =
    FreeVar "init$term$=lbrace=^space'^_term_^space'^=comma=^space'^_term_^space^_string_^space'^=dot=^space'^_term_^space'^=rbrace=" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
      ⟪$⟫ quoteToAnnTerm (List Char ∋ "_") ⟪$⟫ quoteToAnnTerm t₂ -- TODO: add a name to pair?
  Quotable-AnnTerm .quoteToAnnTerm (Phi t t₁ t₂) =
    FreeVar "init$term$=phi=^space^_term_^space^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁ ⟪$⟫ quoteToAnnTerm t₂
  Quotable-AnnTerm .quoteToAnnTerm (Eq-T t t₁) =
    FreeVar "init$term$=equal=^space^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (M-T t) = FreeVar "init$term$=omega=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (Mu t t₁) =
    FreeVar "init$term$=mu=^space^_term_^space^_term_"
      ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Epsilon t) =
    FreeVar "init$term$=epsilon=^space^_term_" ⟪$⟫ quoteToAnnTerm t
  Quotable-AnnTerm .quoteToAnnTerm (Gamma t t₁) =
    FreeVar "init$term$=zeta=CatchErr^space^_term_^space^_term_" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁
  Quotable-AnnTerm .quoteToAnnTerm (Ev x x₁) = □ -- TODO
  Quotable-AnnTerm .quoteToAnnTerm (Char-T x) = FreeVar "init$term$=kappa=_char_" ⟪$⟫ Char-T x
  Quotable-AnnTerm .quoteToAnnTerm (CharEq t t₁) =
    FreeVar "init$term$=gamma=^space^_term_^space^_term_" ⟪$⟫ quoteToAnnTerm t ⟪$⟫ quoteToAnnTerm t₁

  Quotable-PureTerm : Quotable PureTerm
  Quotable-PureTerm .quoteToAnnTerm t = □ -- TODO

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

instance
  Quotable-ProductData : ∀ {L R} ⦃ _ : Quotable L ⦄ ⦃ _ : Quotable R ⦄ → Quotable (ProductData L R)
  Quotable-ProductData .quoteToAnnTerm pDat = let open ProductData pDat in
    FreeVar "init$pair" ⟪$⟫ lType ⟪$⟫ rType ⟪$⟫ quoteToAnnTerm l ⟪$⟫ quoteToAnnTerm r
