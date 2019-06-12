module Class.Show where

open import Data.String using (String)

record Show {a} (A : Set a) : Set a where
  field
    show : A -> String

open Show {{...}} public
