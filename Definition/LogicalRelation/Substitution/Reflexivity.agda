module Definition.LogicalRelation.Substitution.Reflexivity where

open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Data.Product


reflₛ : ∀ {A Γ l}
        ([Γ] : ⊩ₛ Γ)
        ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
      → Γ ⊩ₛ⟨ l ⟩ A ≡ A / [Γ] / [A]
reflₛ [Γ] [A] ⊢Δ [σ] =
  reflEq (proj₁ ([A] ⊢Δ [σ]))

reflₜₛ : ∀ {A t Γ l}
         ([Γ] : ⊩ₛ Γ)
         ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
         ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A])
       → Γ ⊩ₛ⟨ l ⟩t' t ≡ t ∷ A / [Γ] / [A]
reflₜₛ [Γ] [A] [t] ⊢Δ [σ] =
  reflEqTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))
