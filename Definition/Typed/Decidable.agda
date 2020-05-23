{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Decidable where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Decidable
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Consequences.Completeness

open import Tools.Nullary


-- Decidability of conversion of well-formed types
dec : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Dec (Γ ⊢ A ≡ B)
dec ⊢A ⊢B = map soundnessConv↑ completeEq
                (decConv↑ (completeEq (refl ⊢A))
                          (completeEq (refl ⊢B)))

-- Decidability of conversion of well-formed terms
decTerm : ∀ {t u A Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Dec (Γ ⊢ t ≡ u ∷ A)
decTerm ⊢t ⊢u = map soundnessConv↑Term completeEqTerm
                    (decConv↑Term (completeEqTerm (refl ⊢t))
                                  (completeEqTerm (refl ⊢u)))
