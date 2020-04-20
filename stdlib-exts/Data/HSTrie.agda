module Data.HSTrie where

open import Class.Map
open import Data.Char
open import Data.Char.Instance
open import Data.List
open import Data.List.Instance
open import Data.Product
open import Data.String
open import Data.String.Instance
open import Data.Maybe
open import Function

{-#
  FOREIGN GHC
  import Data.Trie
  import Data.Text.Encoding
#-}

data Maybe' (A : Set) : Set where
  nothing' : Maybe' A
  just' : A -> Maybe' A

postulate
  HSTrie : Set -> Set
  emptyTrie : (A : Set) -> HSTrie A
  insertTrie : (A : Set) -> String -> A -> HSTrie A -> HSTrie A
  deleteTrie : (A : Set) -> String -> HSTrie A -> HSTrie A
  lookupTrie : (A : Set) -> String -> HSTrie A -> Maybe' A
  fmapTrie : (A B : Set) -> (A -> B) -> HSTrie A -> HSTrie B
  trieKeysPrim : (A : Set) -> HSTrie A -> List String
  submapTrie : (A : Set) -> String -> HSTrie A -> HSTrie A

maybe'ToMaybe : {A : Set} -> Maybe' A -> Maybe A
maybe'ToMaybe nothing' = nothing
maybe'ToMaybe (just' a) = just a

{-# COMPILE GHC Maybe' = data Maybe (Nothing | Just) #-}
{-# COMPILE GHC HSTrie = type Trie #-}
{-# COMPILE GHC emptyTrie = \ _ -> empty #-}
{-# COMPILE GHC insertTrie = \ _ s -> insert (encodeUtf8 s) #-}
{-# COMPILE GHC deleteTrie = \ _ s -> delete (encodeUtf8 s) #-}
{-# COMPILE GHC lookupTrie = \ _ s -> Data.Trie.lookup (encodeUtf8 s) #-}
{-# COMPILE GHC fmapTrie = \ _ _ -> fmap #-}
{-# COMPILE GHC trieKeysPrim = \ _ -> fmap decodeUtf8 . keys #-}
{-# COMPILE GHC submapTrie = \ _ s -> submap (encodeUtf8 s) #-}

instance
  NDTrie-Map : MapClass String HSTrie
  NDTrie-Map = record
           { insert = insertTrie _
           ; remove = deleteTrie _
           ; lookup = λ s t -> maybe'ToMaybe (lookupTrie _ s t)
           ; mapSnd = fmapTrie _ _
           ; emptyMap = emptyTrie _
           }

trieKeys : ∀ {A} -> HSTrie A -> List String
trieKeys = trieKeysPrim _

lookupHSTrie : ∀ {A} -> String -> HSTrie A -> HSTrie A
lookupHSTrie = submapTrie _
