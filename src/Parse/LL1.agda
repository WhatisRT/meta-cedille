--------------------------------------------------------------------------------
-- This file contains the definition of a context-free grammar, as well as a
-- parser for those grammars that are actually of LL1 type. There is currently
-- no check if the grammar is actually a LL1 grammar, so the parser might loop
-- indefinitely or return an error message in certain cases, even if the string
-- actually matches the grammar.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Parse.LL1 where

import Data.String as S
open import Class.Monad.Except
open import Data.List using (boolDropWhile)
open import Data.String using (fromList; toList; uncons)
open import Data.Sum using (isInj₁)
open import Data.Tree

open import Prelude

record CFG (V : Set) (MultiChar : Set) : Set₁ where
  field
    S : V
    R : V → Set
    AllRules : (v : V) → List (R v)

  -- whether to keep track of the result
  V' : Set
  V' = V × Bool

  field
    Rstring'' : {v : V} → R v → List (V' ⊎ MultiChar ⊎ String)

  private variable v : V

  Terminal : Set
  Terminal = MultiChar ⊎ String

  isMultiChar : Terminal → Bool
  isMultiChar (inj₁ _) = true
  isMultiChar (inj₂ _) = false

  terminalLength : Terminal → ℕ
  terminalLength (inj₁ x) = 1
  terminalLength (inj₂ y) = S.length y

  Rule : Set
  Rule = ∃[ v ] R v

  Rstring : R v → List (V ⊎ MultiChar ⊎ String)
  Rstring r = map (Data.Sum.map₁ proj₁) (Rstring'' r)

  Rstring' : Rule → List (V ⊎ Terminal)
  Rstring' (_ , r) = Rstring r

  SynTree : Set
  SynTree = Tree (Rule ⊎ Char)

  produces-ε : R v → Bool
  produces-ε = null ∘ Rstring

module _ {V MultiChar : Set} (showV : V → String)
  (matchMulti : MultiChar → Char → Bool) (showMulti : MultiChar → String)
  (G : CFG V MultiChar) (M : Set → Set) {{_ : Monad M}} {{_ : MonadExcept M String}} where
  -- we don't care if it is actually a LL1 grammar

  open CFG G

  showTerminal : Terminal → String
  showTerminal (inj₁ x) = showMulti x
  showTerminal (inj₂ y) = y

  match : String → Terminal → Bool
  match s (inj₁ x) with strHead s
  ... | nothing = false
  ... | just c  = matchMulti x c
  match s (inj₂ y) = strTake (strLength y) s ≣ y

  -- select the first rule satisfying the predicate
  firstRule : (v : V) → (R v → Bool) → Maybe (R v)
  firstRule v P = head $ boolDropWhile (not ∘ P) $ AllRules v

  {-# NON_TERMINATING #-}
  parsingTable : V → String → Maybe Rule
  parsingTable v' x = -,_ <$> firstRule v' (startWith x) <∣> firstRule v' produces-ε
                      -- select the first rule starting with x, or the first that is empty
    where
      startWith : {v : V} → String → R v → Bool
      startWith x = helper x ∘ Rstring
        where
          helper : String → List (V ⊎ Terminal) → Bool
          helper x [] = false
          helper x (inj₁ v ∷ rest) with boolFilter (startWith x) (AllRules v)
          ... | [] = if null $ boolFilter produces-ε (AllRules v) then false else helper x rest
          ... | _  = true
          helper x (inj₂ t ∷ _) = match x t

  {-# NON_TERMINATING #-}
  parseWithInitNT : V → String → M (SynTree × String)
  parseWithInitNT v a = do
    (y , rest) ← helper [ inj₁ v ] a
    if strLength a ≣ strLength rest ∧ not (strNull a)
      then throwError ("Could not parse anything from input:\n" + a)
      else maybe
        (λ z → return (z , rest)) (throwError "BUG: Error while creating syntax tree.")
        (resToTree y)
    where
      helper : List (V ⊎ Terminal) → String → M (List (Rule ⊎ Char) × String)
      helper [] s = return ([] , s)
      helper (inj₁ x ∷ stack) s with parsingTable x s
      ... | just r  = map₁ (inj₁ r ∷_) <$> helper (Rstring' r ++ stack) s
      ... | nothing = throwError $
          "No applicable rule found for non-terminal " + showV x + "\nRemaining:\n" + s
      helper (inj₂ y ∷ stack) s with uncons s | match s y
      ... | just (x , _) | true  = let prepend = if isMultiChar y then inj₂ x ∷_ else id
        in map₁ prepend <$> helper stack (strDrop (terminalLength y) s)
      ... | just       _ | false = throwError $
          "Mismatch while parsing characters:\n expected '" + showTerminal y +
          "' but got '" + strTake (strLength $ showTerminal y) s + "'"
      ... | nothing | _ = throwError ("Unexpected end of input while trying to parse " + showTerminal y)

      resToTree : List (Rule ⊎ Char) → Maybe SynTree
      resToTree x = proj₁ <$> resToTree' x
        where
          needsChild : V' ⊎ Terminal → Bool
          needsChild (inj₁ x) = true
          needsChild (inj₂ (inj₁ x)) = true
          needsChild (inj₂ (inj₂ y)) = false

          attachChild : V' ⊎ Terminal → Bool
          attachChild (inj₁ (_ , b)) = b
          attachChild _              = true

          resToTree' : List (Rule ⊎ Char) → Maybe (SynTree × List (Rule ⊎ Char))
          ruleChildren : List (V' ⊎ Terminal) → List (Rule ⊎ Char) → Maybe (List SynTree × List (Rule ⊎ Char))

          resToTree' [] = nothing
          resToTree' (inj₁ l ∷ l₁) with ruleChildren (Rstring'' (proj₂ l)) l₁
          ... | just (fst , snd)   = just (Node (inj₁ l) fst , snd)
          ... | nothing            = nothing
          resToTree' (inj₂ l ∷ l₁) = just (Node (inj₂ l) [] , l₁)

          ruleChildren [] l = just ([] , l)
          ruleChildren (x ∷ s) l with needsChild x | resToTree' l
          ... | false | _               = ruleChildren s l
          ... | true  | just (t , rest) = (if attachChild x then map₁ (t ∷_) else id) <$> ruleChildren s rest
          ... | true  | nothing         = nothing
