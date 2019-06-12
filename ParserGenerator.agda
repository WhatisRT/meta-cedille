--------------------------------------------------------------------------------
-- This file provides the generateCFG function that turns a list of strings of
-- the current syntax for grammars into a grammar as defined in Parser.agda
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module ParserGenerator where

import Data.Product
open import Class.Monad.Except
open import Class.Traversable
open import Data.Fin hiding (_≟_; _+_)
open import Data.Fin.Instance
open import Data.Fin.Map
open import Data.List hiding (lookup; _[_]%=_)
open import Data.String using (toList) renaming (fromList to fromListS)
open import Data.Vec using (Vec; lookup; fromList; []; _∷_; _[_]%=_)
open import Data.Vec.Exts
open import Monads.Except
open import Parser
open import Relation.Nullary
open import Relation.Unary

open import Prelude
open import Prelude.Strings

data Marker : Set where
  NonTerminalBracket : Marker
  NameDivider : Marker

MarkedChar = Char ⊎ Marker
MarkedString = List MarkedChar

instance
  Marker-Eq : Eq Marker
  Marker-Eq = record { _≟_ = λ
    { NonTerminalBracket NonTerminalBracket → yes refl
    ; NonTerminalBracket NameDivider → no (λ ())
    ; NameDivider NonTerminalBracket → no (λ ())
    ; NameDivider NameDivider → yes refl } }

-- Grammar with show functions for rules and non-terminals
Grammar = ∃[ n ] Σ (CFG (Fin (suc n))) (λ G -> (Rules G -> List Char) × (Fin (suc n) -> List Char))

escapeMarker = '\\'
nonTerminalMarker = '_'
nameMarker = '$'
-- other good candidates: =&*:@#~%

showMarkedString : MarkedString -> List Char
showMarkedString [] = []
showMarkedString (inj₁ x ∷ s) = decCase x of
  (escapeMarker , escapeMarker ∷ [ escapeMarker ]) ∷
  (nonTerminalMarker , escapeMarker ∷ [ nonTerminalMarker ]) ∷
  (nameMarker , escapeMarker ∷ [ nameMarker ]) ∷ []
  default [ x ] ++ showMarkedString s
showMarkedString (inj₂ NonTerminalBracket ∷ s) = nonTerminalMarker ∷ showMarkedString s
showMarkedString (inj₂ NameDivider ∷ s) = nameMarker ∷ showMarkedString s

convertToMarked : List Char -> MarkedString
convertToMarked = helper false
  where
    helper : Bool -> List Char -> MarkedString
    helper escaped [] = []
    helper false (x ∷ l) =
      if ⌊ x ≟ escapeMarker ⌋
        then helper true l
        else (if ⌊ x ≟ nonTerminalMarker ⌋
                 then inj₂ NonTerminalBracket ∷ helper false l
                 else (if ⌊ x ≟ nameMarker ⌋
                          then inj₂ NameDivider ∷ helper false l
                          else inj₁ x ∷ helper false l))
    helper true (x ∷ l) = inj₁ x ∷ helper false l

checkRuleName : List Char -> List Char × List MarkedString -> Set
checkRuleName s r = s ≡ proj₁ r

checkRuleNameDec : ∀ s -> Decidable (checkRuleName s)
checkRuleNameDec [] ([] , snd) = yes refl
checkRuleNameDec [] (x ∷ fst , snd) = no (λ ())
checkRuleNameDec (x ∷ s) ([] , snd) = no (λ ())
checkRuleNameDec (x ∷ s) (x₁ ∷ fst , snd) with x ≟ x₁ | checkRuleNameDec s (fst , snd)
... | yes p | yes p₁ rewrite p | p₁ = yes refl
... | yes p | no ¬p = no λ { refl -> ¬p refl }
... | no ¬p | H' = no λ { refl -> ¬p refl }

module GenCFG {M} {{_ : Monad M}} {{_ : MonadExcept M String}} where

  removeMarks : MarkedString -> M (List Char)
  removeMarks [] = return []
  removeMarks (inj₁ x ∷ l) = do
    rest <- removeMarks l
    return (x ∷ rest)
  removeMarks (inj₂ y ∷ l) = throwError "BUG: Error removing marks: Unexpected name divider!"

  preParseCFG : List MarkedString -> M (∃[ n ] Vec (List Char × List MarkedString) n)
  preParseCFG [] = return $ zero , []
  preParseCFG (x ∷ l) with break (_≟ inj₂ NameDivider) x
  ... | name , rule' = if null name
    then throwError $ "Parsing rule has no/empty name! Rule: " + (fromListS $ showMarkedString x)
    else let rule = dropHeadIfAny rule' in do
      _ , rules <- preParseCFG l
      return $ case findIndex (checkRuleNameDec $ showMarkedString name) rules of λ
        { (just x) → -, rules [ x ]%= Data.Product.map id (rule ∷_)
        ; nothing → -, (showMarkedString name , [ rule ]) ∷ rules}

  generateCFG' : ∀ {n : ℕ} -> List Char -> (rules : Vec (List Char × List MarkedString) (suc n))
    -> M Grammar
  generateCFG' {n} start rules = do
    ruleTable <- parseRuleTable
    case findIndex (checkRuleNameDec start) rules of λ
      { (just i) ->
        return $
          (n
          , record
            { S = i
            ; R = λ x → Fin $ numOfRules x
            ; AllRules = λ v → tabulate id
            ; Rstring = λ {v} -> ruleTable v }
          , (λ { (fst , snd) →
               proj₁ (lookup rules fst) ++ "$" ++
               (showMarkedString $ lookup (Data.Vec.fromList $ proj₂ $ lookup rules fst) snd)})
          , λ n -> proj₁ $ lookup rules n)
      ; nothing -> throwError $ "No non-terminal named " + fromListS start + " found!" }
    where
      numOfRules : Fin (suc n) -> ℕ
      numOfRules = length ∘ proj₂ ∘ lookup rules

      RuleTable : Set -> Set
      RuleTable T = DepFinMap (suc n) (λ v -> (FinMap (numOfRules v) T))

      RuleString : Set
      RuleString = List (Fin (suc n) ⊎ Char)

      sequenceRuleTable : ∀ {A} -> RuleTable (M A) -> M (RuleTable A)
      sequenceRuleTable f = sequenceDepFinMap λ v → sequenceDepFinMap (f v)

      ruleToParseRule : MarkedString -> M RuleString
      ruleToParseRule s =
        (sequence $ map removeMarks $ splitMulti (inj₂ NonTerminalBracket) s) >>= helper
        where
          helper : List (List Char) -> M RuleString
          helper [] = return []
          helper (l ∷ []) = return (map inj₂ l)
          helper (l ∷ l₁ ∷ l₂) = do
            s <- maybeToError
              (findIndex (checkRuleNameDec l₁) rules)
              ("Couldn't find a non-terminal named '" + fromListS l₁ + "'")
            rest <- helper l₂
            return (map inj₂ l ++ [ inj₁ s ] ++ rest)

      parseRuleTable : M (RuleTable RuleString)
      parseRuleTable = sequenceRuleTable
        λ v x → ruleToParseRule $ lookup (fromList $ proj₂ (lookup rules v)) x

  -- The first parameter describes the non-terminal the grammar should start with
  generateCFG : List Char -> List (List Char) -> M Grammar
  generateCFG start l = do
    x <- preParseCFG (map convertToMarked l)
    case x of λ
      { (zero , y) → throwError "The grammar is empty!"
      ; (suc k , y) → generateCFG' start y }

open GenCFG public
