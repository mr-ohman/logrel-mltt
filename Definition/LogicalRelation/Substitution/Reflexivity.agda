{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Reflexivity {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product


-- Reflexivity of valid types.
reflₛ : ∀ {A Γ l}
        ([Γ] : ⊩ᵛ Γ)
        ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ≡ A / [Γ] / [A]
reflₛ [Γ] [A] ⊢Δ [σ] =
  reflEq (proj₁ ([A] ⊢Δ [σ]))

-- Reflexivity of valid terms.
reflₜₛ : ∀ {A t Γ l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A])
       → Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A / [Γ] / [A]
reflₜₛ [Γ] [A] [t] ⊢Δ [σ] =
  reflEqTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))
