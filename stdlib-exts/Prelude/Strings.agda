module Prelude.Strings where

import Data.String.Literals
import Data.List.Literals
open import Data.Unit
open import Agda.Builtin.FromString public

instance
  isStringStringPublic = Data.String.Literals.isString
  isStringListPublic = Data.List.Literals.isString

  unitInstance = tt
