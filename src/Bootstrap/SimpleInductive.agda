module Bootstrap.SimpleInductive where

open import Data.List
open import Data.String using (_<+>_; unwords)

open import Prelude

data ConstrData' : Set where
  Self : ConstrData'
  Other : String → ConstrData'

ConstrData = String × List ConstrData'
InductiveData = String × List ConstrData

private
  ℕ⊎Sshow : ℕ ⊎ String → String
  ℕ⊎Sshow (inj₁ x) = show x
  ℕ⊎Sshow (inj₂ y) = y

  ℕ⊎Ssuc : ℕ ⊎ String → ℕ ⊎ String
  ℕ⊎Ssuc (inj₁ x) = inj₁ (suc x)
  ℕ⊎Ssuc (inj₂ y) = inj₂ y

  constrDataToPrefix : (ℕ ⊎ String → String) → ℕ ⊎ String → Char → ConstrData → String
  constrDataToPrefix term n _ (_    , [])         = term n
  constrDataToPrefix term n c (name , x ∷ constr) =
    show c <+> "_ :" <+> (case x of λ { Self → ℕ⊎Sshow n ; (Other y) → y }) <+>
    constrDataToPrefix term (ℕ⊎Ssuc n) c (name , constr)

  constrDataToConstrPrefix : ℕ ⊎ String → Char → ConstrData → String
  constrDataToConstrPrefix = constrDataToPrefix (λ _ → "")

  constrDataToTypeAnn : ℕ ⊎ String → Char → ConstrData → String
  constrDataToTypeAnn = constrDataToPrefix ℕ⊎Sshow

  kthConstr : ℕ → InductiveData → String
  kthConstr k (name , constrs) with lookupMaybe k constrs
  ... | Maybe.just c@(_ , constr) =
    constrDataToConstrPrefix (inj₂ name) 'λ' c <+> -- constructor arguments
    "Λ _ : *" <+>
    unwords (flip mapWithIndex constrs -- abstract arguments
      (λ k constr → "λ _ :" <+> constrDataToTypeAnn (inj₁ k) 'Π' constr)) <+>
    -- apply all abstract arguments to self constructors and leave the others alone
    -- then pass the results to the k-th abstract constructor
    applyTo currentConstr
      (zipWith
        (λ where
          i Self → applyTo
            ("<" + show i <+> show (length constrs) + ">")
            abstractConstrs
          i (Other x) → show i)
        (applyUpTo ((length constrs + length constr) ∸_) $ length constr) constr)
    where
      currentConstr = show (length constrs ∸ k ∸ 1)

      abstractConstrs : List String
      abstractConstrs = reverse $ applyUpTo show $ length constrs

      applyTo : String → List String → String
      applyTo f fs = foldl (λ s l → "[" + s <+> l + "]") f fs
  kthConstr k constrs | nothing = "Error: no such constructor"

  kthConstrType : String → ℕ → List ConstrData → String
  kthConstrType name k constrs with lookupMaybe k constrs
  ... | just x = constrDataToTypeAnn (inj₂ name) 'Π' x
  ... | nothing = "Error: no such constructor"

  typeDecl : String → List ConstrData → String
  typeDecl name constrs =
    "∀ _ : *" <+>
    unwords (flip mapWithIndex constrs (λ k constr →
      "Π _ :" <+> constrDataToTypeAnn (inj₁ k) 'Π' constr)) <+>
    show (length constrs)

--------------------------------------------------------------------------------

simpleInductive : InductiveData → String
simpleInductive d@(name , constrs) =
  "let" <+> name <+> ":=" <+> typeDecl name constrs + "." +
  unwords (flip mapWithIndex constrs
    (λ k constr →
      "let" <+> proj₁ constr <+> ":=" <+> kthConstr k d <+> ":" <+>
      kthConstrType name k constrs + "."))
