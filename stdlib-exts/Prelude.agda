{-# OPTIONS --guardedness #-}

module Prelude where

open import Class.Equality public
open import Class.Functor public
open import Class.Monad public
open import Class.Monoid public
open import Class.Show public
open import Class.Traversable public

open import Data.Bool hiding (_≟_; _<_; _<?_; _≤_; _≤?_) public
open import Data.Bool.Instance public
open import Data.Char using (Char) public
open import Data.Char.Instance public
open import Data.Empty public
open import Data.Empty.Instance public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Fin.Patterns public
open import Data.List using (List; []; [_]; _∷_; drop; boolFilter; filter; head; reverse; _++_; zipWith; foldl; intersperse; map; null; span; break; allFin; length; mapMaybe; or; and; applyUpTo; replicate) public
open import Data.List.Exts public
open import Data.List.Instance public
open import Data.Maybe using (Maybe; just; nothing; maybe; from-just; is-just; is-nothing; _<∣>_) public
open import Data.Maybe.Instance public
open import Data.Nat hiding (_+_; _≟_) public
open import Data.Nat.Instance public
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; -,_; Σ; swap; Σ-syntax; map₁; map₂; <_,_>; curry; uncurry) public
open import Data.Product.Instance public
open import Data.String using (String; uncons; unwords; unlines; padRight; _<+>_) public
open import Data.String.Exts public
open import Data.String.Instance public
open import Data.Sum using (_⊎_; inj₁; inj₂; from-inj₁; from-inj₂) public
open import Data.Sum.Instance public
open import Data.Unit.Instance public
open import Data.Unit.Polymorphic using (⊤; tt) public
open import IO using (IO; putStr; writeFile) public
open import IO.Finite using (getLine) public
open import IO.Exts public
open import IO.Instance public
open import System.Environment public
open import System.Exit public

open import Function public

open import Relation.Nullary using (Dec; yes; no) public
open import Relation.Nullary.Decidable using (⌊_⌋) public
open import Relation.Nullary.Negation public
open import Relation.Unary using (Decidable) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
