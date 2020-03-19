module Data.NDTrie where

open import Class.Map
open import Data.Char
open import Data.Char.Instance
open import Data.List
open import Data.List.Instance
open import Data.AVL.Value
open import Data.Product

import Data.Char.Properties as Char
import Data.Trie Char.<-strictTotalOrder-≈ as T

NDTrie : Set -> Set
NDTrie A = T.Trie (const _ A) _

instance
  NDTrie-Map : MapClass (List Char) NDTrie
  NDTrie-Map = record
           { insert = T.insert
           ; remove = T.deleteValue
           ; lookup = T.lookupValue
           ; mapSnd = λ f -> T.map f
           ; emptyMap = T.empty
           }

trieKeys : ∀ {A} -> NDTrie A -> List (List Char)
trieKeys t = Data.List.map proj₁ (T.toList t)

lookupNDTrie : ∀ {A} -> List Char -> NDTrie A -> NDTrie A
lookupNDTrie [] t = t
lookupNDTrie (c ∷ cs) t = lookupNDTrie cs (T.lookupTrie c t)
