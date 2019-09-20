--------------------------------------------------------------------------------
-- This file contains functions to convert between agda terms and meta-cedille
-- terms
--------------------------------------------------------------------------------

module Conversion where

open import Class.Map
open import Class.Monad.Except
open import Class.Traversable
open import Data.List using (map; length)
open import Data.SimpleMap
open import Data.String using (fromList; toList)
open import Data.Tree
open import Data.Word using (toℕ)
open import Data.Word32

open import CoreTheory
open import InitEnv
open import ParseTreeConvert

open import Prelude
open import Prelude.Strings

module ConversionInternals {M : Set -> Set} {{_ : Monad M}} {{_ : MonadExcept M String}} where
  private
    {-# TERMINATING #-} -- findOutermostConstructor returns a list of smaller terms
    buildConstructorTree : Context -> PureTerm -> Tree PureTerm
    buildConstructorTree Γ t with findOutermostConstructor t
    ... | t' , ts = Node t' $ map (buildConstructorTree Γ) $ reverse ts

    extractConstrId : PureTerm -> M ℕ
    extractConstrId (Var-P (Bound x)) = return $ toℕ x
    extractConstrId (Var-P (Free x)) = throwError "Not a constructor"
    {-# CATCHALL #-}
    extractConstrId t = throwError ("Not a variable" + show t)

    {-# TERMINATING #-}
    extractConstrIdTree : Tree PureTerm -> M (Tree ℕ)
    extractConstrIdTree (Node x y) = do
      x' <- extractConstrId x
      y' <- sequence (map extractConstrIdTree y)
      return $ Node x' y'

    -- converts a normalized term to an appropriate agda term, if possible
    constrsToAgda : {A : Set} -> List Char -> (Tree ℕ -> M A) -> Context -> PureTerm -> M A
    constrsToAgda init toTerm Γ t = do
      t' <- extractConstrIdTree $ buildConstructorTree Γ t
      toTerm t'

  constrsToStmt : Context -> PureTerm -> M Stmt
  constrsToStmt = constrsToAgda "stmt" (λ t -> maybeToError (toStmt t) "Error while converting to stmt")

  constrsToTerm : Context -> PureTerm -> M AnnTerm
  constrsToTerm = constrsToAgda "term" (λ t -> maybeToError (toTerm t) "Error while converting to term")

  constrsToString : Context -> PureTerm -> M String
  constrsToString = constrsToAgda "name" (λ x -> maybeToError (mmap fromList $ toName x) "Error while converting to string")

  constrsToStringList : Context -> PureTerm -> M (List String)
  constrsToStringList = constrsToAgda "name" (λ x -> maybeToError (toNameList x) "Error while converting to string")

open ConversionInternals public

private
  bitToTerm : Bool -> AnnTerm
  bitToTerm false = Var-A $ Free "init$bit$false"
  bitToTerm true = Var-A $ Free "init$bit$true"

  byteToTerm : Byte -> AnnTerm
  byteToTerm (mkByte x0 x1 x2 x3 x4 x5 x6 x7) =
    foldl App-A (Var-A $ Free "init$byte$bits")
      ((bitToTerm x0) ∷ (bitToTerm x1) ∷ (bitToTerm x2) ∷ (bitToTerm x3) ∷
      (bitToTerm x4) ∷ (bitToTerm x5) ∷ (bitToTerm x6) ∷ (bitToTerm x7) ∷ [])

  word32ToTerm : Word32 -> AnnTerm
  word32ToTerm (mkWord32 x0 x1 x2 x3) =
    foldl App-A (Var-A $ Free "init$char$bytes")
      ((byteToTerm x0) ∷ (byteToTerm x1) ∷ (byteToTerm x2) ∷ (byteToTerm x3) ∷ [])

charToTerm : Char -> AnnTerm
charToTerm c = word32ToTerm (charToWord32 c)

charListToTerm : List Char -> AnnTerm
charListToTerm [] = Var-A (Free "init$string$nil")
charListToTerm (c ∷ cs) =
  App-A (App-A (Var-A $ Free "init$string$cons") $ charToTerm c) (charListToTerm cs)

stringToTerm : String -> AnnTerm
stringToTerm = charListToTerm ∘ toList

stringListToTerm : List String -> AnnTerm
stringListToTerm [] = Var-A $ Free "init$stringList$nil"
stringListToTerm (x ∷ l) =
  App-A (App-A (Var-A $ Free "init$stringList$cons") $ charListToTerm $ toList x) $ stringListToTerm l

termToTerm : AnnTerm -> AnnTerm
termToTerm t = Sort-A □ -- TODO

termListToTerm : List AnnTerm -> AnnTerm
termListToTerm [] = Var-A $ Free "init$termList$nil"
termListToTerm (x ∷ l) =
  App-A (App-A (Var-A $ Free "init$termList$cons") $ termToTerm x) $ termListToTerm l

-- The type of results of executing a statement in the interpreter. This can be
-- returned back to the code via embedExecutionResult
MetaResult = List String × List AnnTerm

-- Reflects the result into a term
embedMetaResult : MetaResult -> AnnTerm
embedMetaResult (fst , snd) =
  App-A (App-A (Var-A $ Free "init$metaResult$pair") $ stringListToTerm fst) $ termListToTerm snd
