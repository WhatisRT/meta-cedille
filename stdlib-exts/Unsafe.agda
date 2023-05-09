module Unsafe where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)

private
  variable A B : Set

postulate
  error : {A : Set} → String → A

{-# FOREIGN GHC import Data.Text #-}
{-# COMPILE GHC error = \ _ s -> error (unpack s) #-}

postulate
  undefined : A

{-# COMPILE GHC undefined = undefined #-}

from-just : Maybe A → A
from-just (just a) = a
from-just nothing  = error "from-just"

from-inj₂ : A ⊎ B → B
from-inj₂ (inj₁ a) = error "from-inj₂"
from-inj₂ (inj₂ b) = b
