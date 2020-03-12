module Data.String.Exts where

open import Data.Bool hiding (_<?_)
open import Data.Char hiding (_<?_)
open import Data.String hiding (_<?_)
open import Data.Maybe
open import Data.Nat
open import Data.Product

open import Relation.Nullary.Decidable

data MaybeWrapper {a} (A : Set a) : Set a where
  justWrapper : A -> MaybeWrapper A
  nothingWrapper : MaybeWrapper A

{-# FOREIGN GHC type AgdaMaybe l a = Maybe a #-}
{-# COMPILE GHC MaybeWrapper = data AgdaMaybe (Just | Nothing) #-}

{-#
  FOREIGN GHC
  import Data.Text

  data ResWrapper = ResWrapper Char Data.Text.Text

  unconsWrapped = (fmap (\x -> case x of (a,b) -> ResWrapper a b)) . uncons
#-}

data unconsRes : Set where
  resWrapper : Char -> String -> unconsRes

{-# COMPILE GHC unconsRes = data ResWrapper (ResWrapper) #-}

postulate
  primStrHead : String -> MaybeWrapper Char
  strNull : String -> Bool
  strTake : ℕ -> String -> String
  primUncons : String -> MaybeWrapper unconsRes

{-# COMPILE GHC primStrHead = (fmap fst) . uncons #-}
{-# COMPILE GHC strNull = Data.Text.null #-}
{-# COMPILE GHC strTake = Data.Text.take . fromIntegral #-}
{-# COMPILE GHC primUncons = unconsWrapped #-}

strHead : String -> Maybe Char
strHead s with primStrHead s
strHead s | justWrapper x = just x
strHead s | nothingWrapper = nothing

uncons : String -> Maybe (Char × String)
uncons s with primUncons s
uncons s | justWrapper (resWrapper x x₁) = just (x , x₁)
uncons s | nothingWrapper = nothing

shortenString : ℕ -> String -> String
shortenString l s = if ⌊ length s <? l ⌋ then s else strTake l s ++ "..."
