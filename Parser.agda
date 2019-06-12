{-# OPTIONS --type-in-type #-}

module Parser where

open import Class.Monad.Except
open import Data.String using (fromList)
open import Data.List hiding (lookup; uncons)
open import Data.Maybe using (_<∣>_)
open import Data.String.Exts
open import Data.Tree

open import Monads.Except
open import Monads.Identity
open import Prelude

record CFG (V : Set) : Set₁ where
  field
    S : V
    R : V -> Set
    AllRules : (v : V) -> List (R v)
    Rstring : {v : V} -> R v -> List (V ⊎ Char)

Rules : ∀ {V} -> CFG V -> Set
Rules record { R = R } = ∃[ v ] R v

module LL1Parser {V : Set} {{_ : Eq V}} (G : CFG V) (showV : V -> String) {a}
  (M : Set₁ -> Set a) {{_ : Monad M}} {{_ : MonadExcept M String}} where
  -- we don't care if it is actually a LL1 grammar

  S = CFG.S G
  R = CFG.R G
  Rstring = CFG.Rstring G
  AllRules = CFG.AllRules G

  Rule = Rules G
  Rstring' : Rule -> List (V ⊎ Char)
  Rstring' (fst , snd) = Rstring snd
  SynTree = Tree Rule

  showStack : List (V ⊎ Char) -> String
  showStack [] = ""
  showStack (inj₁ x ∷ s) = showV x + showStack s
  showStack (inj₂ y ∷ s) = fromList [ y ] + showStack s

  {-# NON_TERMINATING #-}
  parsingTable : V -> Maybe Char -> Maybe Rule
  parsingTable v x with R v
  ... | rules =
    head $ map (-,_) $ boolFilter (maybe startWith produces-ε x) (AllRules v)
    where
      produces-ε : {v : V} -> R v -> Bool
      produces-ε r with Rstring r
      ... | [] = true
      ... | x ∷ x₁ = false

      startWith : {v : V} -> Char -> R v -> Bool
      startWith x r = helper x (Rstring r)
        where
          helper : Char -> List (V ⊎ Char) -> Bool
          helper x [] = false
          helper x (inj₁ x₁ ∷ y) = case boolFilter (startWith x) (AllRules x₁) of λ
            { [] → case boolFilter produces-ε (AllRules x₁) of λ
              { [] → false
              ; (_ ∷ r) → helper x y }
            ; (x ∷ z) → true }
          helper x (inj₂ y₁ ∷ y) = x ≣ y₁

  {-# NON_TERMINATING #-}
  parseInit : V -> String -> M (SynTree × String)
  parseInit v a = do
    (y , rest) <- helper [ inj₁ v ] a
    maybe
      (λ z -> return (z , rest)) (throwError "BUG: Error while creating syntax tree.")
      (resToTree y)
    where
      helper : List (V ⊎ Char) -> String -> M (List Rule × String)
      helper [] s = return ([] , s)
      helper (inj₁ x ∷ stack) s with (parsingTable x (strHead s)) <∣> (parsingTable x nothing)
      ... | just x₁ = do
        (res , rest) <- helper ((Rstring' x₁) ++ stack) s
        return ((x₁ ∷ res) , rest)
      ... | nothing = throwError $
          "No applicable rule found for non-terminal " + showV x + "\nRemaining:\n" + s
      helper (inj₂ y ∷ stack) s with uncons s
      ... | just (x , s') = if x ≣ y
        then helper stack s'
        else (throwError $
          "Mismatch while parsing characters: tried to parse " + fromList [ y ] +
          " but got '" + fromList [ x ] + "'\nRemaining:\n" + fromList [ x ] + s')
      ... | nothing = throwError "Unexpected end of input"

      resToTree' : List Rule -> Maybe (SynTree × List Rule)
      resToTree' [] = nothing
      resToTree' (l ∷ l₁) =
        case applyTimes resToTree' (length (boolFilter terminal (Rstring' l))) l₁ of λ
          { (fst , snd) → just ((Node l fst) , snd) }
        where
          applyTimes : ∀ {a b} {A : Set a} {B : Set b}
                     -> (A -> Maybe (B × A)) -> ℕ -> A -> (List B) × A
          applyTimes f zero a = [] , a
          applyTimes f (suc k) a = case f a of λ
            { (just (fst , snd)) →
              case applyTimes f k snd of λ { (fst' , snd') → (fst ∷ fst') , snd' }
            ; nothing → [] , a }

          terminal : V ⊎ Char -> Bool
          terminal (inj₁ x) = true
          terminal (inj₂ y) = false

      resToTree : List Rule -> Maybe SynTree
      resToTree x = Data.Maybe.map proj₁ $ resToTree' x

  parse : String -> M (SynTree × String)
  parse = parseInit S
