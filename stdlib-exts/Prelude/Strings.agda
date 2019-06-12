module Prelude.Strings where

  import Data.String.Literals
  import Data.List.Literals
  open import Agda.Builtin.FromString public
  open import Data.Unit using (⊤) public

  instance
    isStringStringPublic = Data.String.Literals.isString
    isStringListPublic = Data.List.Literals.isString
