module SimpleInductive where

open import Data.String using (fromList)
open import Data.List

open import Prelude

data ConstrData' : Set where
  Self : ConstrData'
  Other : String → ConstrData'

ConstrData = String × List ConstrData'
InductiveData = String × List ConstrData

private

  constrDataToConstrType : String → ConstrData → String
  constrDataToConstrType name (n , []) = name
  constrDataToConstrType name (n , (Self ∷ constr)) =
    "Π _ : " + name + " " + constrDataToConstrType name (n , constr)
  constrDataToConstrType name (n , (Other x ∷ constr)) =
    "Π _ : " + x + " " + constrDataToConstrType name (n , constr)

  ℕ⊎Sshow : ℕ ⊎ String → String
  ℕ⊎Sshow (inj₁ x) = show x
  ℕ⊎Sshow (inj₂ y) = y

  ℕ⊎Ssuc : ℕ ⊎ String → ℕ ⊎ String
  ℕ⊎Ssuc (inj₁ x) = inj₁ (suc x)
  ℕ⊎Ssuc (inj₂ y) = inj₂ y

  constrDataToConstrPrefix : ℕ ⊎ String → Char → ConstrData → String
  constrDataToConstrPrefix n c (name , []) = ""
  constrDataToConstrPrefix n c (name , x ∷ constr) =
    fromList (c ∷ []) + " _ : " + (case x of λ { Self → ℕ⊎Sshow n ; (Other y) → y }) +
    " " + constrDataToConstrPrefix (ℕ⊎Ssuc n) c (name , constr)

  constrDataToTypePrefix : ℕ ⊎ String → Char → ConstrData → String
  constrDataToTypePrefix n c (name , []) = ℕ⊎Sshow n + " "
  constrDataToTypePrefix n c (name , x ∷ constr) =
    fromList (c ∷ []) + " _ : " + (case x of λ { Self → ℕ⊎Sshow n ; (Other y) → y }) +
    " " + constrDataToTypePrefix (ℕ⊎Ssuc n) c (name , constr)

  kthConstr : ℕ → InductiveData → String
  kthConstr k (name , constrs) with lookupMaybe k constrs
  kthConstr k (name , constrs) | Maybe.just c@(_ , constr) =
    constrDataToConstrPrefix (inj₂ name) 'λ' c + -- constructor arguments
    "Λ _ : * " +
    Data.String.concat
      (zipWith
        (λ constr k → "λ _ : " + constrDataToTypePrefix k 'Π' constr)
        constrs (applyUpTo inj₁ (length constrs))) + -- abstract arguments
    -- apply all abstract arguments to self constructors and leave the others alone
    -- then pass the results to the k-th abstract constructor
    applyTo currentConstr
      (zipWith
        (λ i → λ
          { Self → applyTo
            ("<" + show i + " " + show (length constrs) + ">")
            abstractConstrs
          ; (Other x) → show i })
        (applyUpTo ((length constrs + length constr) ∸_) $ length constr) constr)
    where
      currentConstr = show (length constrs ∸ k ∸ 1)

      abstractConstrs : List String
      abstractConstrs = reverse $ applyUpTo (λ i → show i) $ length constrs

      applyTo : String → List String → String
      applyTo f fs = foldl (λ s l → "[" + s + " " + l + "]") f fs
  kthConstr k constrs | nothing = "Error: no such constructor"

  kthConstrType : String → ℕ → List ConstrData → String
  kthConstrType name k constrs with lookupMaybe k constrs
  ... | just x = constrDataToConstrType name x
  ... | nothing = "Error: no such constructor"

  typeDecl : String → List ConstrData → String
  typeDecl name constrs =
    "∀ _ : * " +
    Data.String.concat
      (zipWith
        (λ constr k → "Π _ : " + constrDataToTypePrefix k 'Π' constr)
        constrs
        (applyUpTo inj₁ (length constrs))) +
    show (length constrs)

--------------------------------------------------------------------------------

simpleInductive : InductiveData → String
simpleInductive d@(name , constrs) =
  "let " + name + " := " + typeDecl name constrs + "." +
  Data.String.concat
    (zipWith
      (λ constr k →
        "let " + proj₁ constr + " := " + kthConstr k d + " : " +
        kthConstrType name k constrs + ".")
      constrs
      (applyUpTo id (length constrs)))
