module Class.Monad.Writer where

open import Class.Monad
open import Data.Product
open import Data.Unit.Polymorphic
open import Level
open import Function

private
  variable
    a : Level
    A : Set a

record MonadWriter (M : Set a → Set a) {{_ : Monad M}} (W : Set a) : Set (suc a) where
  field
    tell : W → M ⊤
    listen : M A → M (A × W)
    pass : M (A × (W → W)) → M A

  listens : {B : Set a} → (W → B) → M A → M (A × B)
  listens f x = do
    (a , w) ← listen x
    return (a , f w)

  censor : (W → W) → M A → M A
  censor f x = pass $ do
    a ← x
    return (a , f)

open MonadWriter {{...}} public
