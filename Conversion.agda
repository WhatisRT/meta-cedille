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
open import Data.Word32

open import InitEnv
open import cedille-core
open import cedille-core-parser

open import Prelude
open import Prelude.Strings

module ConversionInternals {M : Set -> Set} {{_ : Monad M}} {{_ : MonadExcept M String}} where
  private
    {-# TERMINATING #-} -- findOutermostConstructor returns a list of smaller terms
    buildConstructorTree : Context -> PureTerm -> Tree PureTerm
    buildConstructorTree Γ t with findOutermostConstructor t
    ... | t' , ts = Node t' $ map (buildConstructorTree Γ) $ reverse ts

    extractConstrId : PureTerm -> M ℕ
    extractConstrId (Var-P (Bound x)) = return x
    extractConstrId (Var-P (Free x)) = throwError "Not a constructor"
    {-# CATCHALL #-}
    extractConstrId t = throwError ("Not a variable" + show t)

    {-# TERMINATING #-}
    extractConstrIdTree : Tree PureTerm -> M (Tree ℕ)
    extractConstrIdTree (Node x y) = do
      x' <- extractConstrId x
      y' <- sequence (map extractConstrIdTree y)
      return $ Node x' y'

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

    charConvert : Tree ℕ -> Maybe (Tree (List Char))
    charConvert t = do
      w <- treeToWord32 t
      return (Node ("char$" ++ [ bytesToChar w ]) [])

    {-# TERMINATING #-}
    ℕTreeToSyntaxTree : List Char -> Tree ℕ -> Maybe (Tree (List Char))
    ℕTreeToSyntaxTree init t@(Node x x₁) =
      if init ≣ "nameInitChar" ∨ init ≣ "nameTailChar"
        then charConvert t
        else do
          rules <- lookup init parseRuleMap
          rule <- lookupMaybe x rules
          rest <- sequence $ zipWith ℕTreeToSyntaxTree (parseConstrToNonTerminals' rule) x₁
          return $ Node rule rest

    -- converts a normalized term to an appropriate agda term, if possible
    constrsToAgda : {A : Set} -> List Char -> (Tree (List Char) -> M A) -> Context -> PureTerm -> M A
    constrsToAgda init toTerm Γ t =
      ((extractConstrIdTree $ buildConstructorTree Γ t) >>= (λ t -> maybeToError (ℕTreeToSyntaxTree init t) "Error while generating syntax tree")) >>= toTerm

  constrsToStmt : Context -> PureTerm -> M Stmt
  constrsToStmt = constrsToAgda "stmt" (λ t -> maybeToError (toStmt t) "Error while converting to stmt")

  constrsToString : Context -> PureTerm -> M String
  constrsToString = constrsToAgda "name" (λ x -> maybeToError (mmap fromList $ toName x) "Error while converting to string")

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
