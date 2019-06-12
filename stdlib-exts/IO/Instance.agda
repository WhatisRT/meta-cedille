module IO.Instance where

open import Class.Monad using (Monad)
open import Class.Monad.IO
open import Class.Monoid
open import Codata.Musical.Notation
open import Data.Product
open import Data.Sum
open import IO
open import Monads.ExceptT
open import Monads.StateT
open import Monads.WriterT

instance
  IO-Monad : ∀ {a} -> Monad (IO {a})
  IO-Monad = record { _>>=_ = λ x f -> (♯ x) >>= λ a -> ♯ f a ; return = return }

IO-MonadIO : ∀ {a} -> MonadIO (IO {a})
IO-MonadIO = record { liftIO = λ x -> x }

ExceptT-MonadIO : ∀ {a b} {M : Set a -> Set b} {E} {{_ : Monad M}} {{_ : MonadIO M}} -> MonadIO (ExceptT M E) {{ExceptT-Monad}}
ExceptT-MonadIO = record { liftIO = λ x -> liftIO (♯ x >>= λ a -> ♯ return (inj₂ a)) }

StateT-MonadIO : ∀ {a b} {M : Set a -> Set b} {S : Set a} {{_ : Monad M}} {{_ : MonadIO M}} -> MonadIO (StateT M S)
StateT-MonadIO = record { liftIO = λ x -> λ s -> liftIO (♯ x >>= (λ a -> ♯ return (a , s))) }

WriterT-MonadIO : ∀ {a b} {M : Set a -> Set b} {W : Set a} {{_ : Monoid W}} {{_ : Monad M}} {{_ : MonadIO M}} -> MonadIO (WriterT M W) {{WriterT-Monad}}
WriterT-MonadIO = record { liftIO = λ x -> liftIO (♯ x >>= λ a -> ♯ return (a , mzero)) }
