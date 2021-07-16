module Class.MonadTrans where

open import Class.Monad
open import Level

record MonadTrans {a} (T : (Set a -> Set a) -> Set a -> Set a) : Set (suc a) where
  field
    embed : {A : Set a} {M : Set a -> Set a} {{_ : Monad M}} -> M A -> T M A

open MonadTrans {{...}} public
