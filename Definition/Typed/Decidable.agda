module Definition.Typed.Decidable where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Decidable
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Validity

open import Tools.Nullary


dec : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Dec (Γ ⊢ A ≡ B)
dec ⊢A ⊢B =
  let ⊢Γ≡Γ = reflConEq (wf ⊢A)
  in  map soundnessConv↑ validEq
          (decConv↑ ⊢Γ≡Γ (validEq (refl ⊢A)) (validEq (refl ⊢B)))

decTerm : ∀ {t u A Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Dec (Γ ⊢ t ≡ u ∷ A)
decTerm ⊢t ⊢u =
  let ⊢Γ≡Γ = reflConEq (wfTerm ⊢t)
  in  map soundnessConv↑Term validEqTerm
          (decConv↑Term ⊢Γ≡Γ (validEqTerm (refl ⊢t)) (validEqTerm (refl ⊢u)))
