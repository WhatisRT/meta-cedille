module Class.Monad.Writer where

  open import Class.Monad
  open import Data.Product
  open import Data.Unit
  open import Level

  record MonadWriter {a b} (M : Set a -> Set b) {{_ : Monad M}} (W : Set a) : Set (suc a ⊔ b) where
    field
      tell : W -> M (Lift a ⊤)
      listen : ∀ {A} -> M A -> M (A × W)
      pass : ∀ {A} -> M (A × (W -> W)) -> M A

  open MonadWriter {{...}} public
