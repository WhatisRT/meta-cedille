--------------------------------------------------------------------------------
-- This file provides the generateCFG function that turns a list of strings of
-- the current syntax for grammars into a grammar as defined in Parser.agda
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Parse.Generate where

open import Class.Monad.Except
open import Data.Fin.Map
import Data.List.NonEmpty as NE
open NE using (List⁺; _∷_)
open import Data.String using (toList; fromChar; uncons) renaming (fromList to fromListS)
open import Data.Vec using (Vec; lookup; fromList; []; _∷_; _[_]%=_)
open import Data.Vec.Exts

open import Parse.LL1
open import Parse.MarkedString
open import Parse.MultiChar
open import Parse.Escape

open import Prelude
open import Prelude.Strings

-- Grammar with show functions for rules and non-terminals
Grammar = ∃[ n ]
  Σ[ G ∈ CFG (Fin (suc n)) MultiChar ] (CFG.Rule G → String) × (Fin (suc n) → String)

NonTerminal : Grammar → Set
NonTerminal (n , _) = Fin (suc n)

initNT : (G : Grammar) → NonTerminal G
initNT (_ , G , _) = CFG.S G

findNT : (G : Grammar) → String → Maybe (NonTerminal G)
findNT (n , _ , _ , showNT) NT = findIndex (NT ≟_) (Data.Vec.tabulate showNT)

checkRuleName : String → String × List MarkedString → Set
checkRuleName s r = s ≡ proj₁ r

checkRuleNameDec : ∀ s → Decidable (checkRuleName s)
checkRuleNameDec s (s' , _) = s ≟ s'

module _ {M} {{_ : Monad M}} {{_ : MonadExcept M String}} where

  -- Read until the closing marker
  bracketHelper : Marker → MarkedString → M (List⁺ String × MarkedString)
  bracketHelper m [] = throwError "Unexpected end of string! Expected a marker!"
  bracketHelper m (inj₁ x ∷ s) = do
    (head ∷ tail , rest) ← bracketHelper m s
    return (fromChar x + head ∷ tail , rest)
  bracketHelper m (inj₂ x ∷ s) =
    if x ≣ m
      then return (NE.[ "" ] , s)
      else
        if x ≣ WildcardSeparator
          then if (m ≣ WildcardBracket true) ∨ (m ≣ WildcardBracket false)
            then (do
              (res , rest) ← bracketHelper m s
              return ("" NE.∷⁺ res , rest))
            else throwError "Found a wildcard separator outside of a wildcard bracket!"
          else throwError "Found unexpected marker!"

  preParseCFG : List MarkedString → M (∃[ n ] Vec (String × List MarkedString) n)
  preParseCFG [] = return $ zero , []
  preParseCFG (x ∷ l) with break (_≟ inj₂ NameDivider) x
  ... | name , rule' = if null name
    then throwError $ "Parsing rule has no/empty name! Rule: " + markedStringToString x
    else do
      _ , rules ← preParseCFG l
      let rule = dropHeadIfAny rule'
      return $ case findIndex (checkRuleNameDec $ markedStringToString name) rules of λ
        { (just x) → -, rules [ x ]%= map₂ (rule ∷_)
        ; nothing → -, (markedStringToString name , [ rule ]) ∷ rules}
  
  {-# TERMINATING #-}
  generateCFG' : ∀ {n} → String → Vec (String × List MarkedString) (suc n) → M Grammar
  generateCFG' {n} start rules = do
    ruleTable ← parseRuleTable
    case findIndex (checkRuleNameDec start) rules of λ where
      (just i) →
        return $
          (-, record
            { S = i
            ; R = Fin ∘ numOfRules
            ; AllRules = allFin ∘ numOfRules
            ; Rstring'' = λ {v} → ruleTable v }
          , (λ where (NT , rule) → let (NT' , rules') = lookup rules NT
                                   in NT' + "$" + markedStringToString (lookup (fromList rules') rule))
          , proj₁ ∘ lookup rules)
      nothing → throwError $ "No non-terminal named " + start + " found!"
    where
      numOfRules : Fin (suc n) → ℕ
      numOfRules = length ∘ proj₂ ∘ lookup rules

      RuleTable : Set → Set
      RuleTable T = DepFinMap (suc n) (λ v → FinMap (numOfRules v) T)

      RuleString : Set
      RuleString = List ((Fin (suc n) × Bool) ⊎ MultiChar ⊎ String)

      sequenceRuleTable : ∀ {A} → RuleTable (M A) → M (RuleTable A)
      sequenceRuleTable f = sequenceDepFinMap (sequenceDepFinMap ∘ f)

      addCharToRuleString : Char → RuleString → RuleString
      addCharToRuleString c [] = [ inj₂ (inj₂ $ fromChar c) ]
      addCharToRuleString c s@(inj₁ _ ∷ _) = inj₂ (inj₂ $ fromChar c) ∷ s
      addCharToRuleString c s@(inj₂ (inj₁ _) ∷ _) = inj₂ (inj₂ $ fromChar c) ∷ s
      addCharToRuleString c (inj₂ (inj₂ y) ∷ s) = inj₂ (inj₂ (fromChar c + y)) ∷ s

      markedStringToRule : MarkedString → M RuleString
      markedStringToRule [] = return []
      markedStringToRule (inj₁ x ∷ s) = do
        res ← markedStringToRule s
        return (addCharToRuleString x res)
      -- this terminates because 'rest' is shorter than 's'
      markedStringToRule (inj₂ (NonTerminalBracket b) ∷ s) = do
        (nonTerm ∷ _ , rest) ← bracketHelper (NonTerminalBracket b) s
        res ← markedStringToRule rest
        nonTerm' ← maybeToError
          (findIndex (checkRuleNameDec nonTerm) rules)
          ("Couldn't find a non-terminal named '" + nonTerm + "'")
        return (inj₁ (nonTerm' , b) ∷ res)
      markedStringToRule (inj₂ NameDivider ∷ s) =
        throwError "The rule cannot contain a name divider!"
      markedStringToRule (inj₂ (WildcardBracket b) ∷ s) = do
        (multiChar , rest) ← bracketHelper (WildcardBracket b) s
        inj₂ (inj₁ $ parseMultiCharNE b multiChar) ∷_ <$> markedStringToRule rest
      markedStringToRule (inj₂ WildcardSeparator ∷ s) =
        throwError "Wildcard separator outside of a wildcard!"

      parseRuleTable : M (RuleTable RuleString)
      parseRuleTable = sequenceRuleTable
        λ v x → let y = lookup (fromList $ proj₂ (lookup rules v)) x in
          appendIfError (markedStringToRule y) (" In: " + show y)

  -- The first parameter describes the non-terminal the grammar should start with
  generateCFGNonEscaped : String → List String → M Grammar
  generateCFGNonEscaped start l = do
    (suc k , y) ← preParseCFG $ map convertToMarked l
      where _ → throwError "The grammar is empty!"
    generateCFG' start y

  -- The first parameter describes the non-terminal the grammar should start with
  generateCFG : String → List String → M Grammar
  generateCFG start l =
    maybe (generateCFGNonEscaped start)
      (throwError "Error while un-escaping parsing rules!")
      (sequence $ ((_<$>_ fromListS) ∘ translate ∘ toList) <$> l)
