{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Conversion {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product


convₛ : ∀ {t A B Γ l}
        ([Γ] : ⊩ₛ Γ)
        ([A]  : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
        ([B]  : Γ ⊩ₛ⟨ l ⟩ B / [Γ])
      → Γ ⊩ₛ⟨ l ⟩  A ≡ B / [Γ] / [A]
      → Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A]
      → Γ ⊩ₛ⟨ l ⟩t t ∷ B / [Γ] / [B]
convₛ [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
  let [σA]     = proj₁ ([A] ⊢Δ [σ])
      [σB]     = proj₁ ([B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
      [σt]     = proj₁ ([t] ⊢Δ [σ])
      [σt≡σ't] = proj₂ ([t] ⊢Δ [σ])
  in  convTerm₁ [σA] [σB] [σA≡σB] [σt]
  ,   λ [σ'] [σ≡σ'] → convEqTerm₁ [σA] [σB] [σA≡σB] ([σt≡σ't] [σ'] [σ≡σ'])

conv₂ₛ : ∀ {t A B Γ l}
         ([Γ] : ⊩ₛ Γ)
         ([A]  : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
         ([B]  : Γ ⊩ₛ⟨ l ⟩ B / [Γ])
       → Γ ⊩ₛ⟨ l ⟩  A ≡ B / [Γ] / [A]
       → Γ ⊩ₛ⟨ l ⟩t t ∷ B / [Γ] / [B]
       → Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A]
conv₂ₛ [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
  let [σA]     = proj₁ ([A] ⊢Δ [σ])
      [σB]     = proj₁ ([B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
      [σt]     = proj₁ ([t] ⊢Δ [σ])
      [σt≡σ't] = proj₂ ([t] ⊢Δ [σ])
  in  convTerm₂ [σA] [σB] [σA≡σB] [σt]
  ,   λ [σ'] [σ≡σ'] → convEqTerm₂ [σA] [σB] [σA≡σB] ([σt≡σ't] [σ'] [σ≡σ'])

convEqₛ : ∀ {t u A B Γ l}
        ([Γ] : ⊩ₛ Γ)
        ([A]  : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
        ([B]  : Γ ⊩ₛ⟨ l ⟩ B / [Γ])
      → Γ ⊩ₛ⟨ l ⟩  A ≡ B / [Γ] / [A]
      → Γ ⊩ₛ⟨ l ⟩t' t ≡ u ∷ A / [Γ] / [A]
      → Γ ⊩ₛ⟨ l ⟩t' t ≡ u ∷ B / [Γ] / [B]
convEqₛ [Γ] [A] [B] [A≡B] [t≡u] ⊢Δ [σ] =
  let [σA]     = proj₁ ([A] ⊢Δ [σ])
      [σB]     = proj₁ ([B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
  in  convEqTerm₁ [σA] [σB] [σA≡σB] ([t≡u] ⊢Δ [σ])
