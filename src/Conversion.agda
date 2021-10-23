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
    extractConstrId t = throwError ("Not a variable" + show t)

    {-# TERMINATING #-}
    extractConstrIdTree : Tree PureTerm → M (Tree (ℕ ⊎ Char))
    extractConstrIdTree (Node x y) = do
      x' ← extractConstrId x
      y' ← sequence (map extractConstrIdTree y)
      return $ Node x' y'

    -- converts a normalized term to an appropriate agda term, if possible
    constrsToAgda : {A : Set} → List Char → (Tree (ℕ ⊎ Char) → M A) → Context → PureTerm → M A
    constrsToAgda init toTerm Γ t = do
      t' ← extractConstrIdTree $ buildConstructorTree Γ t
      toTerm t'

  constrsToStmt : Context → PureTerm → M Stmt
  constrsToStmt = constrsToAgda "stmt" (λ t → maybeToError (toStmt t) ("Error while converting to stmt. Tree:\n" + show {{Tree-Show}} t))

  constrsToTerm : Context → PureTerm → M AnnTerm
  constrsToTerm = constrsToAgda "term" (λ t → maybeToError (toTerm t) "Error while converting to term")

  constrsToString : Context → PureTerm → M String
  constrsToString = constrsToAgda "name" (λ x → maybeToError (toName x) "Error while converting to string")

  constrsToStringList : Context → PureTerm → M (List String)
  constrsToStringList = constrsToAgda "name" (λ x → maybeToError (toNameList x) "Error while converting to string")

charListToTerm : List Char → AnnTerm
charListToTerm [] = FreeVar "init$string$nil"
charListToTerm (c ∷ cs) = FreeVar "init$string$cons" ⟪$⟫ Char-A c ⟪$⟫ charListToTerm cs

stringToTerm : String → AnnTerm
stringToTerm = charListToTerm ∘ toList

stringListToTerm : List String → AnnTerm
stringListToTerm [] = FreeVar "init$stringList$nil"
stringListToTerm (x ∷ l) =
  FreeVar "init$stringList$cons" ⟪$⟫ charListToTerm (toList x) ⟪$⟫ stringListToTerm l

-- Quote an AnnTerm
termToTerm : AnnTerm → AnnTerm
termToTerm t = Sort-A □ -- TODO

-- Quote a PureTerm
pureTermToTerm : PureTerm → AnnTerm
pureTermToTerm t = Sort-A □ -- TODO

termListToTerm : List AnnTerm → AnnTerm
termListToTerm [] = FreeVar "init$termList$nil"
termListToTerm (x ∷ l) = FreeVar "init$termList$cons" ⟪$⟫ termToTerm x ⟪$⟫ termListToTerm l

-- The type of results of executing a statement in the interpreter. This can be
-- returned back to the code via embedExecutionResult
MetaResult = List String × List AnnTerm

forceMetaResult : MetaResult → MetaResult
forceMetaResult (fst , snd) = (_,_ $! fst) $! snd

-- Reflects the result into a term
embedMetaResult : MetaResult → AnnTerm
embedMetaResult (fst , snd) =
  FreeVar "init$metaResult$pair" ⟪$⟫ stringListToTerm fst ⟪$⟫ termListToTerm snd
