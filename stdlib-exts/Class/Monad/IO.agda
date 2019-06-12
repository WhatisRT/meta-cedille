module Class.Monad.IO where

  open import Class.Monad
  open import IO
  open import Level

  record MonadIO {a b} (M : Set a -> Set b) {{_ : Monad M}} : Set (suc a ⊔ b) where
    field
      liftIO : ∀ {A : Set a} -> IO A -> M A

  open MonadIO {{...}} public
