{-# OPTIONS --without-K #-}

open import Definition.EqualityRelation

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


ℕₛ : ∀ {Γ l} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ]
ℕₛ [Γ] ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ _ x₂ → id (ℕ ⊢Δ)

ℕₜₛ : ∀ {Γ} ([Γ] : ⊩ₛ Γ)
    → Γ ⊩ₛ⟨ ¹ ⟩t ℕ ∷ U / [Γ] / Uₛ [Γ]
ℕₜₛ [Γ] ⊢Δ [σ] = let ⊢ℕ  = ℕ ⊢Δ
                     [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                 in  Uₜ ℕ (idRedTerm:*: ⊢ℕ) ℕ (≅ₜ-ℕrefl ⊢Δ) [ℕ]
                 ,   (λ x x₁ → Uₜ₌ ℕ ℕ (idRedTerm:*: ⊢ℕ) (idRedTerm:*: ⊢ℕ) ℕ ℕ
                                   (≅ₜ-ℕrefl ⊢Δ) [ℕ] [ℕ] (id (ℕ ⊢Δ)))

zeroₛ : ∀ {Γ} ([Γ] : ⊩ₛ Γ)
      → Γ ⊩ₛ⟨ ¹ ⟩t zero ∷ ℕ / [Γ] / ℕₛ [Γ]
zeroₛ [Γ] ⊢Δ [σ] =
  ℕₜ zero (idRedTerm:*: (zero ⊢Δ)) (≅ₜ-zerorefl ⊢Δ) zero tt
    , (λ _ x₁ → ℕₜ₌ zero zero (idRedTerm:*: (zero ⊢Δ)) (idRedTerm:*: (zero ⊢Δ))
                    (≅ₜ-zerorefl ⊢Δ) zero)

sucₛ : ∀ {Γ n l} ([Γ] : ⊩ₛ Γ)
         ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
     → Γ ⊩ₛ⟨ l ⟩t n ∷ ℕ / [Γ] / [ℕ]
     → Γ ⊩ₛ⟨ l ⟩t suc n ∷ ℕ / [Γ] / [ℕ]
sucₛ ⊢Γ [ℕ] [n] ⊢Δ [σ] =
  sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
  , (λ x x₁ → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x x₁))
