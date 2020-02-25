{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Unit {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Irrelevance

open import Tools.Unit
open import Tools.Product


-- Validity of the Unit type.
Unitᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ]
Unitᵛ [Γ] ⊢Δ [σ] = Unitᵣ (idRed:*: (Unitⱼ ⊢Δ)) , λ _ x₂ → id (Unitⱼ ⊢Δ)

-- Validity of the Unit type as a term.
Unitᵗᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ Unit ∷ U / [Γ] / Uᵛ [Γ]
Unitᵗᵛ [Γ] ⊢Δ [σ] = let ⊢Unit  = Unitⱼ ⊢Δ
                        [Unit] = Unitᵣ (idRed:*: (Unitⱼ ⊢Δ))
                 in  Uₜ Unit (idRedTerm:*: ⊢Unit) Unitₙ (≅ₜ-Unitrefl ⊢Δ) [Unit]
                 ,   (λ x x₁ → Uₜ₌ Unit Unit (idRedTerm:*: ⊢Unit) (idRedTerm:*: ⊢Unit) Unitₙ Unitₙ
                                   (≅ₜ-Unitrefl ⊢Δ) [Unit] [Unit] (id (Unitⱼ ⊢Δ)))

-- Validity of star.
starᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ star ∷ Unit / [Γ] / Unitᵛ [Γ]
starᵛ [Γ] ⊢Δ [σ] =
  Unitₜ star (idRedTerm:*: (starⱼ ⊢Δ)) (≅ₜ-starrefl ⊢Δ) starᵣ
    , (λ _ x₁ → Unitₜ₌ star star (idRedTerm:*: (starⱼ ⊢Δ)) (idRedTerm:*: (starⱼ ⊢Δ))
                    (≅ₜ-starrefl ⊢Δ)) --starᵣ)

-- Validity of η-unit.
η-unitᵛ : ∀ {Γ l e e'} ([Γ] : ⊩ᵛ Γ)
  ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ])
  ([e] : Γ ⊩ᵛ⟨ l ⟩ e ∷ Unit / [Γ] / [Unit])
  ([e'] : Γ ⊩ᵛ⟨ l ⟩ e' ∷ Unit / [Γ] / [Unit])
  → Γ ⊩ᵛ⟨ l ⟩ e ≡ e' ∷ Unit / [Γ] / [Unit]
η-unitᵛ {Γ} {l} {e} {e'} [Γ] [Unit] [e] [e'] {Δ} {σ} ⊢Δ [σ] =
  let J = proj₁ ([Unit] ⊢Δ [σ])
      [σe] = proj₁ ([e] ⊢Δ [σ])
      [σe'] = proj₁ ([e'] ⊢Δ [σ])
      UnitJ : Δ ⊩⟨ l ⟩ Unit
      UnitJ = Unitᵣ (idRed:*: (Unitⱼ ⊢Δ))
      [σe] = irrelevanceTerm J UnitJ [σe]
      [σe'] = irrelevanceTerm J UnitJ [σe']
      ⊢σe = escapeTerm UnitJ [σe]
      ⊢σe' = escapeTerm UnitJ [σe']
  in  irrelevanceEqTerm UnitJ J
                        (Unitₜ₌ _ _
                          (idRedTerm:*: ⊢σe)
                          (idRedTerm:*: ⊢σe')
                          (≅ₜ-η-unit ⊢σe ⊢σe'))
