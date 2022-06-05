module Data.Map.Char where

open import Class.Map
open import Data.Char
open import Data.Char.Instance
open import Data.List
open import Data.Maybe
open import Data.Product

open import Foreign.Haskell

private
  variable C V : Set

postulate
  CharMap : Set → Set

private
  postulate
    fromListCMPrim : List (Pair Char V) → CharMap V
    insertCM       : Char → V → CharMap V → CharMap V
    removeCM       : Char → CharMap V → CharMap V
    lookupCM       : Char → CharMap V → Maybe V
    mapSndCM       : (V → C) → CharMap V → CharMap C
    emptyMapCM     : CharMap V

{-#
  FOREIGN GHC
  import qualified Data.Map.Strict as S
#-}

{-# COMPILE GHC CharMap        = type S.Map Char   #-}
{-# COMPILE GHC fromListCMPrim = \ _ -> S.fromList #-}
{-# COMPILE GHC insertCM       = \ _ -> S.insert   #-}
{-# COMPILE GHC removeCM       = \ _ -> S.delete   #-}
{-# COMPILE GHC lookupCM       = \ _ -> S.lookup   #-}
{-# COMPILE GHC mapSndCM       = \ _ _ -> S.map    #-}
{-# COMPILE GHC emptyMapCM     = \ _ -> S.empty    #-}

fromListCM : List (Char × V) → CharMap V
fromListCM l = fromListCMPrim (Data.List.map toForeignPair l)

instance
  MapClass-CharMap : MapClass Char CharMap
  MapClass-CharMap = record
                       { insert = insertCM
                       ; remove = removeCM
                       ; lookup = lookupCM
                       ; mapSnd = mapSndCM
                       ; emptyMap = emptyMapCM
                       }
