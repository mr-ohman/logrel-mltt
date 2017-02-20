open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product

import Tools.PropositionalEquality as PE


Uₛ : ∀ {Γ} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ]
Uₛ [Γ] ⊢Δ [σ] = U (U ⁰ 0<1 ⊢Δ) , λ _ x₂ → PE.refl

univₛ : ∀ {A Γ l l'} ([Γ] : ⊩ₛ Γ)
        ([U] : Γ ⊩ₛ⟨ l ⟩ U / [Γ])
      → Γ ⊩ₛ⟨ l ⟩t A ∷ U / [Γ] / [U]
      → Γ ⊩ₛ⟨ l' ⟩ A / [Γ]
univₛ {l' = l'} [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = maybeEmb' {l'} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ [σ'] [σ≡σ'] → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁
                                       ((proj₂ ([A] ⊢Δ [σ])) [σ'] [σ≡σ']))

univEqₛ : ∀ {A B Γ l l'} ([Γ] : ⊩ₛ Γ)
          ([U] : Γ ⊩ₛ⟨ l' ⟩ U / [Γ])
          ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
        → Γ ⊩ₛ⟨ l' ⟩t' A ≡ B ∷ U / [Γ] / [U]
        → Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A]
univEqₛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
