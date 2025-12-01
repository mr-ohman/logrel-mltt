{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Trunc {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    F : Term n
    G : Term n
    Γ : Con Term n

-- Validity of ∥.
∥ᵛ : ∀ {n} {Γ : Con Term n} {F l}
     ([Γ] : ⊩ᵛ Γ)
     ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
   → Γ ⊩ᵛ⟨ l ⟩ ∥ F ∥ / [Γ]
∥ᵛ {n} {Γ} {F} {l} [Γ] [F] {k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ′} [σ′] = [F] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ′} [σ′] = escape (proj₁ ([F]σ {σ′} [σ′]))
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢∥F∥ = ∥ ⊢F [σ] ∥ⱼ
  in ∥ᵣ′ (subst σ F)
         (PE.subst
           (λ x → Δ ⊢ x :⇒*: ∥ subst σ F ∥)
           (PE.sym (∥-subst σ F))
           (idRed:*: ⊢∥F∥))
         (⊢F [σ])
         (≅-∥-cong ⊢F≡F)
         (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
  , λ {σ′} [σ′] [σ≡σ′] →
      ∥₌ (subst σ′ F)
         (PE.subst
            (λ x → Δ ⊢ x ⇒* ∥ subst σ′ F ∥)
            (PE.sym (∥-subst _ F))
            (id (∥ ⊢F [σ′] ∥ⱼ)))
         (≅-∥-cong
            (escapeEq (proj₁ ([F] ⊢Δ [σ])) (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])))
         (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))

-- Validity of ∥-congruence.
∥-congᵛ : ∀ {F H l}
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
          ([H] : Γ ⊩ᵛ⟨ l ⟩ H / [Γ])
          ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H / [Γ] / [F])
        → Γ ⊩ᵛ⟨ l ⟩ ∥ F ∥ ≡ ∥ H ∥ / [Γ] / ∥ᵛ {F = F} [Γ] [F]
∥-congᵛ {Γ = Γ} {F} {H} {l} [Γ] [F] [H] [F≡H] {σ = σ} ⊢Δ [σ] =
  let [∥F∥]  = ∥ᵛ {F = F} [Γ] [F]
      [σ∥F∥] = proj₁ ([∥F∥] ⊢Δ [σ])
      l′ , ∥ᵣ F′ D′ ⊢F′ A≡A′ [F]′ = extractMaybeEmb (∥-elim [σ∥F∥])
      [σF]   = proj₁ ([F] ⊢Δ [σ])
      ⊢σH    = escape (proj₁ ([H] ⊢Δ [σ]))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
  in  ∥₌ (subst σ H)
         (id (∥ ⊢σH ∥ⱼ))
         (≅-∥-cong ⊢σF≡σH)
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                        eqA = PE.sym (wk-subst F)
                        eqB = PE.sym (wk-subst H)
                        p = proj₁ ([F] ⊢Δ₁ [ρσ])
                        wut : _ ⊩⟨ _ ⟩ U.wk _ (subst σ F)
                        wut = [F]′ ρ ⊢Δ₁
                        A≡B = [F≡H] ⊢Δ₁ [ρσ]
                    in  irrelevanceEq″ eqA eqB p wut A≡B)

-- Validity of ∥ as a term.
∥ᵗᵛ : ∀ {Γ : Con Term n} {F} ([Γ] : ⊩ᵛ_ {n} Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ]
    → Γ ⊩ᵛ⟨ ¹ ⟩ ∥ F ∥ ∷ U / [Γ] / Uᵛ [Γ]
∥ᵗᵛ {Γ = Γ} {F} [Γ] [Fₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let ⊢Fₜ   = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢F≡Fₜ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) (reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ])))
      [F]₀  = univᵛ {A = F} [Γ] (Uᵛ [Γ]) [Fₜ]
      [∥F∥] = (∥ᵛ {F = F} [Γ] [F]₀) ⊢Δ [σ]
  in Uₜ (∥ subst σ F ∥)
         (PE.subst (λ x → Δ ⊢ x :⇒*: ∥ subst σ F ∥ ∷ U) (PE.sym (∥-subst σ F)) (idRedTerm:*: (∥ ⊢Fₜ ∥ⱼ)))
         ∥ₙ
         (≅ₜ-∥-cong ⊢F≡Fₜ) (proj₁ [∥F∥])
   , λ {σ′} [σ′] [σ≡σ′] →
         let ⊢Fₜ′  = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ′]))
             ⊢F≡F′ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₂ ([Fₜ] ⊢Δ [σ]) [σ′] [σ≡σ′])
             [∥F∥]′ = (∥ᵛ {F = F} [Γ] [F]₀) ⊢Δ [σ′]
         in  Uₜ₌ (∥ subst σ F ∥)
                 (∥ subst σ′ F ∥)
                 (PE.subst
                   (λ x → Δ ⊢ x :⇒*: ∥ subst σ F ∥ ∷ U)
                   (PE.sym (∥-subst σ F))
                   (idRedTerm:*: (∥ ⊢Fₜ ∥ⱼ)))
                 (PE.subst
                   (λ x → Δ ⊢ x :⇒*: ∥ subst σ′ F ∥ ∷ U)
                   (PE.sym (∥-subst σ′ F))
                   (idRedTerm:*: (∥ ⊢Fₜ′ ∥ⱼ)))
                 ∥ₙ ∥ₙ (≅ₜ-∥-cong ⊢F≡F′)
                 (proj₁ [∥F∥]) (proj₁ [∥F∥]′) (proj₂ [∥F∥] [σ′] [σ≡σ′])

-- Validity of ∥-congruence as a term equality.
∥-congᵗᵛ : ∀ {Γ : Con Term n} {F H}
           ([Γ] : ⊩ᵛ_ {n} Γ)
           ([F]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ])
           ([H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ H ∷ U / [Γ] / Uᵛ [Γ])
           ([F≡H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ≡ H ∷ U / [Γ] / Uᵛ [Γ])
         → Γ ⊩ᵛ⟨ ¹ ⟩ ∥ F ∥ ≡ ∥ H ∥ ∷ U / [Γ] / Uᵛ [Γ]
∥-congᵗᵛ {F = F} {H}
         [Γ] [F]ₜ [H]ₜ [F≡H]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]ᵤ = univᵛ {A = F} [Γ] (Uᵛ [Γ]) [F]ₜ
      [H]ᵤ = univᵛ {A = H} [Γ] (Uᵛ [Γ]) [H]ₜ
      [F≡H]ᵤ = univEqᵛ {A = F} {H} [Γ] (Uᵛ [Γ]) [F]ᵤ [F≡H]ₜ
      ∥F∥ₜ = ∥ escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([F]ₜ ⊢Δ [σ])) ∥ⱼ
      ∥H∥ₜ = ∥ escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([H]ₜ ⊢Δ [σ])) ∥ⱼ
  in  Uₜ₌ (∥ subst σ F ∥)
          (∥ subst σ H ∥)
          (PE.subst
            (λ x → Δ ⊢ x :⇒*: ∥ subst σ F ∥ ∷ U)
            (PE.sym (∥-subst σ F))
            (idRedTerm:*: ∥F∥ₜ))
          (PE.subst
            (λ x → Δ ⊢ x :⇒*: ∥ subst σ H ∥ ∷ U)
            (PE.sym (∥-subst σ H))
            (idRedTerm:*: ∥H∥ₜ))
          ∥ₙ ∥ₙ
          (≅ₜ-∥-cong (escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) ([F≡H]ₜ ⊢Δ [σ])))
          (proj₁ (∥ᵛ {F = F} [Γ] [F]ᵤ ⊢Δ [σ]))
          (proj₁ (∥ᵛ {F = H} [Γ] [H]ᵤ ⊢Δ [σ]))
          (∥-congᵛ {F = F} {H} [Γ] [F]ᵤ [H]ᵤ [F≡H]ᵤ ⊢Δ [σ])
