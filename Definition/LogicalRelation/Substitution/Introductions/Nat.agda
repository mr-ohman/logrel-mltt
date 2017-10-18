{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Nat {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Unit
open import Tools.Product


-- Validity of the natural number type.
ℕᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ]
ℕᵛ [Γ] ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ _ x₂ → id (ℕ ⊢Δ)

-- Validity of the natural number type as a term.
ℕᵗᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ ℕ ∷ U / [Γ] / Uᵛ [Γ]
ℕᵗᵛ [Γ] ⊢Δ [σ] = let ⊢ℕ  = ℕ ⊢Δ
                     [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                 in  Uₜ ℕ (idRedTerm:*: ⊢ℕ) ℕ (≅ₜ-ℕrefl ⊢Δ) [ℕ]
                 ,   (λ x x₁ → Uₜ₌ ℕ ℕ (idRedTerm:*: ⊢ℕ) (idRedTerm:*: ⊢ℕ) ℕ ℕ
                                   (≅ₜ-ℕrefl ⊢Δ) [ℕ] [ℕ] (id (ℕ ⊢Δ)))

-- Validity of zero.
zeroᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ zero ∷ ℕ / [Γ] / ℕᵛ [Γ]
zeroᵛ [Γ] ⊢Δ [σ] =
  ℕₜ zero (idRedTerm:*: (zero ⊢Δ)) (≅ₜ-zerorefl ⊢Δ) zero
    , (λ _ x₁ → ℕₜ₌ zero zero (idRedTerm:*: (zero ⊢Δ)) (idRedTerm:*: (zero ⊢Δ))
                    (≅ₜ-zerorefl ⊢Δ) zero)

-- Validity of successor of valid natural numbers.
sucᵛ : ∀ {Γ n l} ([Γ] : ⊩ᵛ Γ)
         ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
     → Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ / [Γ] / [ℕ]
     → Γ ⊩ᵛ⟨ l ⟩ suc n ∷ ℕ / [Γ] / [ℕ]
sucᵛ ⊢Γ [ℕ] [n] ⊢Δ [σ] =
  sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
  , (λ x x₁ → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x x₁))
