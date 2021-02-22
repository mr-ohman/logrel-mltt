{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Validity of the universe type.
Uᵛ : ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ]
Uᵛ [Γ] ⊢Δ [σ] = Uᵣ′ ⁰ 0<1 ⊢Δ , λ _ x₂ → PE.refl

-- Valid terms of type U are valid types.
univᵛ : ∀ {A l l′} ([Γ] : ⊩ᵛ Γ)
        ([U] : Γ ⊩ᵛ⟨ l ⟩ U / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ∷ U / [Γ] / [U]
      → Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]
univᵛ {l′ = l′} [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = maybeEmb′ {l = l′} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ [σ′] [σ≡σ′] → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁
                                       ((proj₂ ([A] ⊢Δ [σ])) [σ′] [σ≡σ′]))

-- Valid term equality of type U is valid type equality.
univEqᵛ : ∀ {A B l l′} ([Γ] : ⊩ᵛ Γ)
          ([U] : Γ ⊩ᵛ⟨ l′ ⟩ U / [Γ])
          ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        → Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B ∷ U / [Γ] / [U]
        → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
univEqᵛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
