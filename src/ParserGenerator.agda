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
open import Data.List.NonEmpty using (List⁺; uncons)
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
  BlacklistWildcardBracket : Marker
  WhitelistWildcardBracket : Marker
  WildcardSeparator : Marker

instance
  Marker-Show : Show Marker
  Marker-Show = record { show = λ
    { NonTerminalBracket → "NonTerminalBracket"
    ; NameDivider → "NameDivider"
    ; BlacklistWildcardBracket → "BlacklistWildcardBracket"
    ; WhitelistWildcardBracket → "WhitelistWildcardBracket"
    ; WildcardSeparator → "WildcardSeparator"} }

enumerateMarkers : List Marker
enumerateMarkers =
  NonTerminalBracket ∷
  NameDivider ∷
  BlacklistWildcardBracket ∷
  WhitelistWildcardBracket ∷
  WildcardSeparator ∷ []

markerRepresentation : Marker -> Char
markerRepresentation NonTerminalBracket = '_'
markerRepresentation NameDivider = '$'
markerRepresentation BlacklistWildcardBracket = '!'
markerRepresentation WhitelistWildcardBracket = '@'
markerRepresentation WildcardSeparator = '&'
-- other good candidates: &*#~%

escapeMarker = '\\'

MarkedChar = Char ⊎ Marker
MarkedString = List MarkedChar

instance
  Marker-Eq : Eq Marker
  Marker-Eq = record { _≟_ = λ
    { NonTerminalBracket NonTerminalBracket → yes refl
    ; NonTerminalBracket NameDivider → no (λ ())
    ; NonTerminalBracket BlacklistWildcardBracket → no (λ ())
    ; NonTerminalBracket WhitelistWildcardBracket → no (λ ())
    ; NonTerminalBracket WildcardSeparator → no (λ ())
    ; NameDivider NonTerminalBracket → no (λ ())
    ; NameDivider NameDivider → yes refl
    ; NameDivider BlacklistWildcardBracket → no (λ ())
    ; NameDivider WhitelistWildcardBracket → no (λ ())
    ; NameDivider WildcardSeparator → no (λ ())
    ; BlacklistWildcardBracket NonTerminalBracket → no (λ ())
    ; BlacklistWildcardBracket NameDivider → no (λ ())
    ; BlacklistWildcardBracket BlacklistWildcardBracket → yes refl
    ; BlacklistWildcardBracket WhitelistWildcardBracket → no (λ ())
    ; BlacklistWildcardBracket WildcardSeparator → no (λ ())
    ; WhitelistWildcardBracket NonTerminalBracket → no (λ ())
    ; WhitelistWildcardBracket NameDivider → no (λ ())
    ; WhitelistWildcardBracket BlacklistWildcardBracket → no (λ ())
    ; WhitelistWildcardBracket WhitelistWildcardBracket → yes refl
    ; WhitelistWildcardBracket WildcardSeparator → no (λ ())
    ; WildcardSeparator NonTerminalBracket → no (λ ())
    ; WildcardSeparator NameDivider → no (λ ())
    ; WildcardSeparator BlacklistWildcardBracket → no (λ ())
    ; WildcardSeparator WhitelistWildcardBracket → no (λ ())
    ; WildcardSeparator WildcardSeparator → yes refl} }

  Marker-EqB = Eq→EqB {{Marker-Eq}}

MultiCharGroup : Set
MultiCharGroup = ⊥

MultiChar' : Set
MultiChar' = List (Char ⊎ MultiCharGroup)

MultiChar : Set
MultiChar = MultiChar' × Bool

showMultiChar : MultiChar -> String
showMultiChar = show

multiCharFromString : List⁺ Char -> MultiChar'
multiCharFromString (head Data.List.NonEmpty.∷ []) = [ inj₁ head ]
multiCharFromString (head Data.List.NonEmpty.∷ x ∷ tail) = []

multiChar'FromList : List (List Char) -> MultiChar'
multiChar'FromList [] = []
multiChar'FromList (l ∷ l₁) =
  (maybe (λ l' -> multiCharFromString l') [] $ Data.List.NonEmpty.fromList l) ++
  multiChar'FromList l₁

multiCharFromList : List (List Char) -> MultiChar
multiCharFromList l = (multiChar'FromList l , true)

negateMultiChar : MultiChar -> MultiChar
negateMultiChar = Data.Product.map₂ not

matchMulti : Char -> MultiChar -> Bool
matchMulti c (fst , snd) with or $ map (helper c) fst
  where
    helper : Char -> Char ⊎ MultiCharGroup -> Bool
    helper c (inj₁ x) = c ≣ x
    helper c (inj₂ ())
... | matches = not (snd xor matches) -- true iff 'snd' equals 'matches'

-- Grammar with show functions for rules and non-terminals
Grammar = ∃[ n ]
  Σ (CFG (Fin (suc n)) MultiChar) (λ G -> (Rules G -> List Char) × (Fin (suc n) -> List Char))

showMarkedString : MarkedString -> List Char
showMarkedString [] = []
showMarkedString (inj₁ x ∷ s) =
  decCase x of
    map (λ x → (x , escapeMarker ∷ [ x ])) $
      -- if we find anything in this list, escape it
      escapeMarker ∷ map markerRepresentation enumerateMarkers
    default [ x ]
  ++ showMarkedString s
showMarkedString (inj₂ x ∷ s) = markerRepresentation x ∷ showMarkedString s

convertToMarked : List Char -> MarkedString
convertToMarked = helper false
  where
    helper : Bool -> List Char -> MarkedString
    helper escaped [] = []
    helper false (x ∷ l) =
      decCase x of
        (escapeMarker , helper true l) ∷
        map (λ x → (markerRepresentation x , inj₂ x ∷ helper false l)) enumerateMarkers
        default (inj₁ x ∷ helper false l)
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

  bracketHelper : Marker -> MarkedString -> M (List⁺ (List Char) × MarkedString)
  bracketHelper m [] = throwError "Unexpected end of string! Expected a marker!"
  bracketHelper m (inj₁ x ∷ s) = do
    (res , rest) <- bracketHelper m s
    case Data.List.NonEmpty.uncons res of λ
      { (head , tail) → return ((x ∷ head) Data.List.NonEmpty.∷ tail , rest) }
  bracketHelper m (inj₂ x ∷ s) =
    if x ≣ m
      then return (Data.List.NonEmpty.[ [] ] , s)
      else
        if (m ≣ BlacklistWildcardBracket) ∨ (m ≣ WhitelistWildcardBracket)
          then if x ≣ WildcardSeparator
            then (do
              (res , rest) <- bracketHelper m s
              return ([] Data.List.NonEmpty.∷ Data.List.NonEmpty.toList res , rest))
            else throwError "Unexpected marker in a wildcard"
          else throwError "This function must be applied with a wildcard bracket"

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

  {-# TERMINATING #-}
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
      RuleString = List (Fin (suc n) ⊎ MultiChar ⊎ String)

      sequenceRuleTable : ∀ {A} -> RuleTable (M A) -> M (RuleTable A)
      sequenceRuleTable f = sequenceDepFinMap λ v → sequenceDepFinMap (f v)

      addCharToRuleString : Char -> RuleString -> RuleString
      addCharToRuleString c [] = [ (inj₂ $ inj₂ $ Data.String.fromChar c) ]
      addCharToRuleString c s@(inj₁ _ ∷ _) = (inj₂ $ inj₂ $ Data.String.fromChar c) ∷ s
      addCharToRuleString c s@(inj₂ (inj₁ _) ∷ _) = (inj₂ $ inj₂ $ Data.String.fromChar c) ∷ s
      addCharToRuleString c (inj₂ (inj₂ y) ∷ s) = (inj₂ $ inj₂ ((Data.String.fromChar c) + y)) ∷ s

      markedStringToRule : MarkedString -> M RuleString
      markedStringToRule [] = return []
      markedStringToRule (inj₁ x ∷ s) = do
        res <- markedStringToRule s
        return (addCharToRuleString x res)
      -- this terminates because 'rest' is shorter than 's'
      markedStringToRule (inj₂ NonTerminalBracket ∷ s) = do
        (nonTerm' , rest) <- bracketHelper NonTerminalBracket s
        case nonTerm' of λ
          { (nonTerm Data.List.NonEmpty.∷ tail) → do
            res <- markedStringToRule rest
            nonTerm' <- maybeToError
              (findIndex (checkRuleNameDec nonTerm) rules)
              ("Couldn't find a non-terminal named '" + fromListS nonTerm + "'")
            return (inj₁ nonTerm' ∷ res) }
      markedStringToRule (inj₂ NameDivider ∷ s) =
        throwError "The rule cannot contain a name divider!"
      markedStringToRule (inj₂ BlacklistWildcardBracket ∷ s) = do
        (multiChar , rest) <- bracketHelper BlacklistWildcardBracket s
        res <- markedStringToRule rest
        return
          ((inj₂ $ inj₁ $ negateMultiChar $ multiCharFromList $
            Data.List.NonEmpty.toList multiChar) ∷ res)
      markedStringToRule (inj₂ WhitelistWildcardBracket ∷ s) = do
        (multiChar , rest) <- bracketHelper WhitelistWildcardBracket s
        res <- markedStringToRule rest
        return ((inj₂ $ inj₁ $ multiCharFromList $ Data.List.NonEmpty.toList multiChar) ∷ res)
      markedStringToRule (inj₂ WildcardSeparator ∷ s) =
        throwError "Wildcard separator outside of a wildcard!"

      parseRuleTable : M (RuleTable RuleString)
      parseRuleTable = sequenceRuleTable
        λ v x → let y = lookup (fromList $ proj₂ (lookup rules v)) x in
          appendIfError (markedStringToRule y) (" In: " + show y)

  -- The first parameter describes the non-terminal the grammar should start with
  generateCFG : List Char -> List (List Char) -> M Grammar
  generateCFG start l = do
    x <- preParseCFG (map convertToMarked l)
    case x of λ
      { (zero , y) → throwError "The grammar is empty!"
      ; (suc k , y) → generateCFG' start y }

open GenCFG public
