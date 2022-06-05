module Data.Map.String where

open import Class.Map
open import Data.String
open import Data.String.Instance
open import Data.List
open import Data.Maybe
open import Data.Product

open import Foreign.Haskell

open import Data.Nat

private
  variable C V : Set

postulate
  StringMap : Set → Set

private
  postulate
    fromListSMPrim : List (Pair String V) → StringMap V
    insertSM       : String → V → StringMap V → StringMap V
    removeSM       : String → StringMap V → StringMap V
    lookupSM       : String → StringMap V → Maybe V
    mapSndSM       : (V → C) → StringMap V → StringMap C
    emptyMapSM     : StringMap V

{-#
  FOREIGN GHC
  import Data.Text
  import qualified Data.Map.Strict as S
#-}

{-# COMPILE GHC StringMap        = type S.Map Text #-}
{-# COMPILE GHC fromListSMPrim = \ _ -> S.fromList #-}
{-# COMPILE GHC insertSM       = \ _ -> S.insert   #-}
{-# COMPILE GHC removeSM       = \ _ -> S.delete   #-}
{-# COMPILE GHC lookupSM       = \ _ -> S.lookup   #-}
{-# COMPILE GHC mapSndSM       = \ _ _ -> S.map    #-}
{-# COMPILE GHC emptyMapSM     = \ _ -> S.empty    #-}

fromListSM : List (String × V) → StringMap V
fromListSM l = fromListSMPrim (Data.List.map toForeignPair l)

instance
  MapClass-StringMap : MapClass String StringMap
  MapClass-StringMap = record
                       { insert = insertSM
                       ; remove = removeSM
                       ; lookup = lookupSM
                       ; mapSnd = mapSndSM
                       ; emptyMap = emptyMapSM
                       }
