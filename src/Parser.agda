--------------------------------------------------------------------------------
-- This file contains the definition of a context-free grammar, as well as a
-- parser for those grammars that are actually of LL1 type. There is currently
-- no check if the grammar is actually a LL1 grammar, so the parser might loop
-- indefinitely or return an error message in certain cases, even if the string
-- actually matches the grammar.
--------------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Parser where

open import Data.Sum using (isInj₁)
open import Class.Monad.Except
open import Data.String using (fromList)
open import Data.List hiding (lookup; uncons)
open import Data.Maybe using (_<∣>_)
open import Data.String.Exts
open import Data.Tree

open import Monads.Except
open import Monads.Identity
open import Prelude

record CFG (V : Set) (MultiChar : Set) : Set₁ where
  field
    S : V
    R : V -> Set
    AllRules : (v : V) -> List (R v)
    Rstring : {v : V} -> R v -> List (V ⊎ MultiChar ⊎ String)

Rules : ∀ {V M} -> CFG V M -> Set
Rules record { R = R } = ∃[ v ] R v

module LL1Parser {V : Set} {{_ : Eq V}} (showV : V -> String) {a}
  {MultiChar : Set} (matchMulti : Char -> MultiChar -> Bool) (showMulti : MultiChar -> String)
  (G : CFG V MultiChar) (M : Set₁ -> Set a) {{_ : Monad M}} {{_ : MonadExcept M String}} where
  -- we don't care if it is actually a LL1 grammar

  S = CFG.S G
  R = CFG.R G
  Rstring = CFG.Rstring G
  AllRules = CFG.AllRules G
  Terminal = MultiChar ⊎ String

  Rule = Rules G
  Rstring' : Rule -> List (V ⊎ Terminal)
  Rstring' (fst , snd) = Rstring snd
  SynTree = Tree (Rule ⊎ Char)

  match : String -> Terminal -> Bool
  match s (inj₁ x) with strHead s
  ... | nothing = false
  ... | just c = matchMulti c x
  match s (inj₂ y) = strTake (length (Data.String.toList y)) s ≣ y

  terminalLength : Terminal -> ℕ
  terminalLength (inj₁ x) = 1
  terminalLength (inj₂ y) = length (Data.String.toList y)

  showChar : Char -> String
  showChar c = fromList [ c ]

  showCharOrMulti : Terminal -> String
  showCharOrMulti (inj₁ x) = showMulti x
  showCharOrMulti (inj₂ y) = y

  showStack : List (V ⊎ Char) -> String
  showStack [] = ""
  showStack (inj₁ x ∷ s) = showV x + showStack s
  showStack (inj₂ y ∷ s) = showChar y + showStack s

  {-# NON_TERMINATING #-}
  parsingTable : V -> String -> Maybe Rule
  parsingTable v x with R v
  ... | rules =
    mmap (-,_)
      (head (boolDropWhile (not ∘ (startWith x)) (AllRules v)) <∣>
      (head (boolDropWhile (not ∘ produces-ε) (AllRules v))))
    where
      produces-ε : {v : V} -> R v -> Bool
      produces-ε r = null $ Rstring r

      startWith : {v : V} -> String -> R v -> Bool
      startWith x r = helper x (Rstring r)
        where
          helper : String -> List (V ⊎ Terminal) -> Bool
          helper x [] = false
          helper x (inj₁ x₁ ∷ y) = case boolFilter (startWith x) (AllRules x₁) of λ
            { [] → case boolFilter produces-ε (AllRules x₁) of λ
              { [] → false
              ; (_ ∷ r) → helper x y }
            ; (x ∷ z) → true }
          helper x (inj₂ y₁ ∷ y) = match x y₁

  {-# NON_TERMINATING #-}
  parseInit : V -> String -> M (SynTree × String)
  parseInit v a = do
    (y , rest) <- helper [ inj₁ v ] a
    maybe
      (λ z -> return (z , rest)) (throwError "BUG: Error while creating syntax tree.")
      (resToTree y)
    where
      helper : List (V ⊎ Terminal) -> String -> M (List (Rule ⊎ Char) × String)
      helper [] s = return ([] , s)
      helper (inj₁ x ∷ stack) s with (parsingTable x s)
      ... | just x₁ = do
        (res , rest) <- helper ((Rstring' x₁) ++ stack) s
        return ((inj₁ x₁ ∷ res) , rest)
      ... | nothing = throwError $
          "No applicable rule found for non-terminal " + showV x + "\nRemaining:\n" + s
      helper (inj₂ y ∷ stack) s with uncons s
      ... | just (x , s') = if match s y
        then (do
          (res₁ , res₂) <- helper stack (strDrop (terminalLength y) s)
          return ((case isInj₁ y of λ { (just _) → [ inj₂ x ] ; nothing → [] }) ++ res₁ , res₂))
        else (throwError $
          "Mismatch while parsing characters: tried to parse " + showCharOrMulti y +
          " but got '" + s + "'")
      ... | nothing = throwError ("Unexpected end of input while trying to parse " + showCharOrMulti y)

      resToTree' : List (Rule ⊎ Char) -> Maybe (SynTree × List (Rule ⊎ Char))
      resToTree' [] = nothing
      resToTree' (inj₁ l ∷ l₁) =
        case applyTimes resToTree' (length (boolFilter terminal (Rstring' l))) l₁ of λ
          { (fst , snd) → just ((Node (inj₁ l) fst) , snd) }
        where
          applyTimes : ∀ {a b} {A : Set a} {B : Set b}
                     -> (A -> Maybe (B × A)) -> ℕ -> A -> (List B) × A
          applyTimes f zero a = [] , a
          applyTimes f (suc k) a = case f a of λ
            { (just (fst , snd)) →
              case applyTimes f k snd of λ { (fst' , snd') → (fst ∷ fst') , snd' }
            ; nothing → [] , a }

          terminal : V ⊎ Terminal -> Bool
          terminal (inj₁ x) = true
          terminal (inj₂ (inj₁ x)) = true
          terminal (inj₂ (inj₂ y)) = false
      resToTree' (inj₂ l ∷ l₁) = just (Node (inj₂ l) [] , l₁)

      resToTree : List (Rule ⊎ Char) -> Maybe SynTree
      resToTree x = Data.Maybe.map proj₁ $ resToTree' x

  parse : String -> M (SynTree × String)
  parse = parseInit S
