{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Union {{eqrel : EqRelSet}} where
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

-- Validity of ∪.
∪ᵛ : ∀ {n} {Γ : Con Term n} {F G l}
     ([Γ] : ⊩ᵛ Γ)
     ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
     ([G] : Γ ⊩ᵛ⟨ l ⟩ G / [Γ])
   → Γ ⊩ᵛ⟨ l ⟩ F ∪ G / [Γ]
∪ᵛ {n} {Γ} {F} {G} {l} [Γ] [F] [G] {k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ′} [σ′] = [F] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ′} [σ′] = escape (proj₁ ([F]σ {σ′} [σ′]))
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      [G]σ {σ′} [σ′] = [G] {σ = σ′} ⊢Δ [σ′]
      [σG] = proj₁ ([G]σ [σ])
      ⊢G {σ′} [σ′] = escape (proj₁ ([G]σ {σ′} [σ′]))
      ⊢G≡G = escapeEq [σG] (reflEq [σG])
      ⊢F∪G = ⊢F [σ] ∪ⱼ ⊢G [σ]
  in ∪ᵣ′ (subst σ F)
         (subst σ G)
         (PE.subst
           (λ x → Δ ⊢ x :⇒*: subst σ F ∪ subst σ G)
           (PE.sym (∪-subst σ F G))
           (idRed:*: ⊢F∪G))
         (⊢F [σ]) (⊢G [σ])
         (≅-∪-cong ⊢F≡F ⊢G≡G)
         (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
         (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σG])
  , λ {σ′} [σ′] [σ≡σ′] →
      ∪₌ (subst σ′ F) (subst σ′ G)
         (PE.subst
            (λ x → Δ ⊢ x ⇒* subst σ′ F ∪ subst σ′ G)
            (PE.sym (∪-subst _ F G))
            (id (⊢F [σ′] ∪ⱼ ⊢G [σ′])))
         (≅-∪-cong
            (escapeEq (proj₁ ([F] ⊢Δ [σ])) (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
            (escapeEq (proj₁ ([G] ⊢Δ [σ])) (proj₂ ([G] ⊢Δ [σ]) [σ′] [σ≡σ′])))
         (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
         (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σG] (proj₂ ([G] ⊢Δ [σ]) [σ′] [σ≡σ′]))

-- Validity of ∪-congruence.
∪-congᵛ : ∀ {F G H E l}
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
          ([G] : Γ ⊩ᵛ⟨ l ⟩ G / [Γ])
          ([H] : Γ ⊩ᵛ⟨ l ⟩ H / [Γ])
          ([E] : Γ ⊩ᵛ⟨ l ⟩ E / [Γ])
          ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H / [Γ] / [F])
          ([G≡E] : Γ ⊩ᵛ⟨ l ⟩ G ≡ E / [Γ] / [G])
        → Γ ⊩ᵛ⟨ l ⟩ F ∪ G ≡ H ∪ E / [Γ] / ∪ᵛ {F = F} {G} [Γ] [F] [G]
∪-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} [Γ] [F] [G] [H] [E] [F≡H] [G≡E] {σ = σ} ⊢Δ [σ] =
  let [∪FG]  = ∪ᵛ {F = F} {G} [Γ] [F] [G]
      [σ∪FG] = proj₁ ([∪FG] ⊢Δ [σ])
      l′ , ∪ᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ = extractMaybeEmb (∪-elim [σ∪FG])
      [σF]   = proj₁ ([F] ⊢Δ [σ])
      [σG]   = proj₁ ([G] ⊢Δ [σ])
      ⊢σH    = escape (proj₁ ([H] ⊢Δ [σ]))
      ⊢σE    = escape (proj₁ ([E] ⊢Δ [σ]))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] ⊢Δ [σ])
  in  ∪₌ (subst σ H)
         (subst σ E)
         (id (⊢σH ∪ⱼ ⊢σE))
         (≅-∪-cong ⊢σF≡σH ⊢σG≡σE)
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                        eqA = PE.sym (wk-subst F)
                        eqB = PE.sym (wk-subst H)
                        p = proj₁ ([F] ⊢Δ₁ [ρσ])
                        wut : _ ⊩⟨ _ ⟩ U.wk _ (subst σ F)
                        wut = [F]′ ρ ⊢Δ₁
                        A≡B = [F≡H] ⊢Δ₁ [ρσ]
                    in  irrelevanceEq″ eqA eqB p wut A≡B)
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                        eqA = PE.sym (wk-subst G)
                        eqB = PE.sym (wk-subst E)
                        p = proj₁ ([G] ⊢Δ₁ [ρσ])
                        wut : _ ⊩⟨ _ ⟩ U.wk _ (subst σ G)
                        wut = [G]′ ρ ⊢Δ₁
                        A≡B = [G≡E] ⊢Δ₁ [ρσ]
                    in  irrelevanceEq″ eqA eqB p wut A≡B)

-- Validity of ∪ as a term.
∪ᵗᵛ : ∀ {Γ : Con Term n} {F G} ([Γ] : ⊩ᵛ_ {n} Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ]
    → Γ ⊩ᵛ⟨ ¹ ⟩ G ∷ U / [Γ] / Uᵛ [Γ]
    → Γ ⊩ᵛ⟨ ¹ ⟩ F ∪ G ∷ U / [Γ] / Uᵛ [Γ]
∪ᵗᵛ {Γ = Γ} {F} {G} [Γ] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let ⊢Fₜ   = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢F≡Fₜ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) (reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ])))
      ⊢Gₜ   = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Gₜ] ⊢Δ [σ]))
      ⊢G≡Gₜ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) (reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Gₜ] ⊢Δ [σ])))
      [F]₀  = univᵛ {A = F} [Γ] (Uᵛ [Γ]) [Fₜ]
      [G]₀  = univᵛ {A = G} [Γ] (Uᵛ [Γ]) [Gₜ]
      [∪FG] = (∪ᵛ {F = F} {G} [Γ] [F]₀ [G]₀) ⊢Δ [σ]
  in Uₜ (subst σ F ∪ subst σ G)
         (PE.subst (λ x → Δ ⊢ x :⇒*: subst σ F ∪ subst σ G ∷ U) (PE.sym (∪-subst σ F G)) (idRedTerm:*: (⊢Fₜ ∪ⱼ ⊢Gₜ)))
         ∪ₙ
         (≅ₜ-∪-cong ⊢F≡Fₜ ⊢G≡Gₜ) (proj₁ [∪FG])
   , λ {σ′} [σ′] [σ≡σ′] →
         let ⊢Fₜ′  = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ′]))
             ⊢Gₜ′  = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Gₜ] ⊢Δ [σ′]))
             ⊢F≡F′ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₂ ([Fₜ] ⊢Δ [σ]) [σ′] [σ≡σ′])
             ⊢G≡G′ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₂ ([Gₜ] ⊢Δ [σ]) [σ′] [σ≡σ′])
             [∪FG]′ = (∪ᵛ {F = F} {G} [Γ] [F]₀ [G]₀) ⊢Δ [σ′]
         in  Uₜ₌ (subst σ F ∪ subst σ G)
                 (subst σ′ F ∪ subst σ′ G)
                 (PE.subst
                   (λ x → Δ ⊢ x :⇒*: subst σ F ∪ subst σ G ∷ U)
                   (PE.sym (∪-subst σ F G))
                   (idRedTerm:*: (⊢Fₜ ∪ⱼ ⊢Gₜ)))
                 (PE.subst
                   (λ x → Δ ⊢ x :⇒*: subst σ′ F ∪ subst σ′ G ∷ U)
                   (PE.sym (∪-subst σ′ F G))
                   (idRedTerm:*: (⊢Fₜ′ ∪ⱼ ⊢Gₜ′)))
                 ∪ₙ ∪ₙ (≅ₜ-∪-cong ⊢F≡F′ ⊢G≡G′)
                 (proj₁ [∪FG]) (proj₁ [∪FG]′) (proj₂ [∪FG] [σ′] [σ≡σ′])

-- Validity of ∪-congruence as a term equality.
∪-congᵗᵛ : ∀ {Γ : Con Term n} {F G H E}
           ([Γ] : ⊩ᵛ_ {n} Γ)
           ([F]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ])
           ([G]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ G ∷ U / [Γ] / Uᵛ [Γ])
           ([H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ H ∷ U / [Γ] / Uᵛ [Γ])
           ([E]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ E ∷ U / [Γ] / Uᵛ [Γ])
           ([F≡H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ≡ H ∷ U / [Γ] / Uᵛ [Γ])
           ([G≡E]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ G ≡ E ∷ U / [Γ] / Uᵛ [Γ])
         → Γ ⊩ᵛ⟨ ¹ ⟩ F ∪ G ≡ H ∪ E ∷ U / [Γ] / Uᵛ [Γ]
∪-congᵗᵛ {F = F} {G} {H} {E}
         [Γ] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]ᵤ = univᵛ {A = F} [Γ] (Uᵛ [Γ]) [F]ₜ
      [G]ᵤ = univᵛ {A = G} [Γ] (Uᵛ [Γ]) [G]ₜ
      [H]ᵤ = univᵛ {A = H} [Γ] (Uᵛ [Γ]) [H]ₜ
      [E]ᵤ = univᵛ {A = E} [Γ] (Uᵛ [Γ]) [E]ₜ
      [F≡H]ᵤ = univEqᵛ {A = F} {H} [Γ] (Uᵛ [Γ]) [F]ᵤ [F≡H]ₜ
      [G≡E]ᵤ = univEqᵛ {A = G} {E} [Γ] (Uᵛ [Γ]) [G]ᵤ [G≡E]ₜ
      ∪FGₜ =    (escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([F]ₜ ⊢Δ [σ])))
             ∪ⱼ (escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([G]ₜ ⊢Δ [σ])))
      ∪HEₜ =    (escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([H]ₜ ⊢Δ [σ])))
             ∪ⱼ (escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([E]ₜ ⊢Δ [σ])))
  in  Uₜ₌ (subst σ F ∪ subst σ G)
          (subst σ H ∪ subst σ E)
          (PE.subst
            (λ x → Δ ⊢ x :⇒*: subst σ F ∪ subst σ G ∷ U)
            (PE.sym (∪-subst σ F G))
            (idRedTerm:*: ∪FGₜ))
          (PE.subst
            (λ x → Δ ⊢ x :⇒*: subst σ H ∪ subst σ E ∷ U)
            (PE.sym (∪-subst σ H E))
            (idRedTerm:*: ∪HEₜ))
          ∪ₙ ∪ₙ
          (≅ₜ-∪-cong (escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) ([F≡H]ₜ ⊢Δ [σ]))
                     (escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) ([G≡E]ₜ ⊢Δ [σ])))
          (proj₁ (∪ᵛ {F = F} {G} [Γ] [F]ᵤ [G]ᵤ ⊢Δ [σ]))
          (proj₁ (∪ᵛ {F = H} {E} [Γ] [H]ᵤ [E]ᵤ ⊢Δ [σ]))
          (∪-congᵛ {F = F} {G} {H} {E} [Γ] [F]ᵤ [G]ᵤ [H]ᵤ [E]ᵤ [F≡H]ᵤ [G≡E]ᵤ ⊢Δ [σ])
