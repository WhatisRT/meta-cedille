module Data.HSTrie where

open import Class.Map
open import Data.List
open import Data.String
open import Data.String.Instance
open import Data.Maybe

private
  variable
    A B : Set

{-#
  FOREIGN GHC
  import Data.Trie
  import Data.Text.Encoding
#-}

postulate
  HSTrie : Set -> Set
  emptyTrie : HSTrie A
  insertTrie : String -> A -> HSTrie A -> HSTrie A
  deleteTrie : String -> HSTrie A -> HSTrie A
  lookupTrie : String -> HSTrie A -> Maybe A
  fmapTrie : (A -> B) -> HSTrie A -> HSTrie B
  trieKeysPrim : HSTrie A -> List String
  submapTrie : String -> HSTrie A -> HSTrie A

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
           { insert = insertTrie
           ; remove = deleteTrie
           ; lookup = lookupTrie
           ; mapSnd = fmapTrie
           ; emptyMap = emptyTrie
           }

trieKeys : HSTrie A -> List String
trieKeys = trieKeysPrim

lookupHSTrie : String -> HSTrie A -> HSTrie A
lookupHSTrie = submapTrie
