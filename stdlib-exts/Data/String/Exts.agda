module Data.String.Exts where

open import Data.Bool hiding (_<?_)
open import Data.Char hiding (_<?_)
open import Data.String hiding (_<?_)
open import Data.Maybe
open import Data.Nat

open import Relation.Nullary.Decidable

{-#
  FOREIGN GHC
  import Data.Text
#-}

postulate
  strHead : String -> Maybe Char
  strNull : String -> Bool
  strTake : ℕ -> String -> String
  strDrop : ℕ -> String -> String
  stripPrefix : String -> String -> Maybe String
  strLength : String -> ℕ

{-# COMPILE GHC strHead = (fmap fst) . uncons #-}
{-# COMPILE GHC strNull = Data.Text.null #-}
{-# COMPILE GHC strTake = Data.Text.take . fromIntegral #-}
{-# COMPILE GHC strDrop = Data.Text.drop . fromIntegral #-}
{-# COMPILE GHC stripPrefix = stripPrefix #-}
{-# COMPILE GHC strLength = toInteger . Data.Text.length #-}

shortenString : ℕ -> String -> String
shortenString l s = if ⌊ length s <? l ⌋ then s else strTake l s ++ "..."
