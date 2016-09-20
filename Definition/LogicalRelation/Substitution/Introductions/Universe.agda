module Definition.LogicalRelation.Substitution.Introductions.Universe where

open import Definition.Untyped
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Data.Product

import Relation.Binary.PropositionalEquality as PE


Uₛ : ∀ {Γ} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ]
Uₛ [Γ] ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ _ x₂ → PE.refl

univₛ : ∀ {A Γ l l'} ([Γ] : ⊩ₛ Γ)
        ([U] : Γ ⊩ₛ⟨ l ⟩ U / [Γ])
      → Γ ⊩ₛ⟨ l ⟩t A ∷ U / [Γ] / [U]
      → Γ ⊩ₛ⟨ l' ⟩ A / [Γ]
univₛ {l' = ⁰} [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))
  in  [A]₁ , (λ x x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x x₁))
univₛ {A} {l' = ¹} [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ x x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x x₁))

univEqₛ : ∀ {A B Γ l l'} ([Γ] : ⊩ₛ Γ)
          ([U] : Γ ⊩ₛ⟨ l' ⟩ U / [Γ])
          ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
        → Γ ⊩ₛ⟨ l' ⟩t' A ≡ B ∷ U / [Γ] / [U]
        → Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A]
univEqₛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])

univₛ₁ : ∀ {A Γ} ([Γ] : ⊩ₛ Γ)
        ([U] : Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ])
      → Γ ⊩ₛ⟨ ¹ ⟩t A ∷ U / [Γ] / [U]
      → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]
univₛ₁ [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ x x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x x₁))
