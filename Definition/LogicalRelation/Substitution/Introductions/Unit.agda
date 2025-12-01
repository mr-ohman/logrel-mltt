{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Unit {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Irrelevance

open import Tools.Nat
open import Tools.Unit
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Validity of the Unit type.
Unitᵛ : ∀ {l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ]
Unitᵛ [Γ] ⊢Δ [σ] = Unitᵣ (idRed:*: (Unitⱼ ⊢Δ)) , λ _ x₂ → id (Unitⱼ ⊢Δ)

-- Validity of the Unit type as a term.
Unitᵗᵛ : ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ Unit ∷ U / [Γ] / Uᵛ [Γ]
Unitᵗᵛ [Γ] ⊢Δ [σ] = let ⊢Unit  = Unitⱼ ⊢Δ
                        [Unit] = Unitᵣ (idRed:*: (Unitⱼ ⊢Δ))
                    in  Uₜ Unit (idRedTerm:*: ⊢Unit) Unitₙ (≅ₜ-Unitrefl ⊢Δ) [Unit]
                    ,   (λ x x₁ → Uₜ₌ Unit Unit (idRedTerm:*: ⊢Unit) (idRedTerm:*: ⊢Unit) Unitₙ Unitₙ
                                      (≅ₜ-Unitrefl ⊢Δ) [Unit] [Unit] (id (Unitⱼ ⊢Δ)))

[Unit]-prop-star : {k : Nat} {Δ : Con Term k}
                 → [Unit]-prop Δ star star
[Unit]-prop-star {k} {Δ} = starᵣ , starᵣ

-- Validity of star.
starᵛ : ∀ {l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ star ∷ Unit / [Γ] / Unitᵛ [Γ]
starᵛ [Γ] ⊢Δ [σ] =
  Unitₜ star (idRedTerm:*: (starⱼ ⊢Δ)) (≅ₜ-starrefl ⊢Δ) starᵣ
    , (λ _ x₁ → Unitₜ₌ star star
                       [ starⱼ ⊢Δ , starⱼ ⊢Δ , id (starⱼ ⊢Δ) ]
                       [ starⱼ ⊢Δ , starⱼ ⊢Δ , id (starⱼ ⊢Δ) ]
                       (≅ₜ-starrefl ⊢Δ) [Unit]-prop-star)

η-unit′ : ∀ {l e e'}
            ([Unit] : Γ ⊩⟨ l ⟩Unit Unit)
            ([e]    : Γ ⊩⟨ l ⟩ e ∷ Unit / Unit-intr [Unit])
            ([e']   : Γ ⊩⟨ l ⟩ e' ∷ Unit / Unit-intr [Unit])
          → Γ ⊩⟨ l ⟩ e ≡ e' ∷ Unit / Unit-intr [Unit]
η-unit′ {Γ = Γ} {l} {e} {e'}
        [Unit]@(noemb x)
        [e]@(Unitₜ n [ ⊢e , ⊢n , d ] k≡k prop)
        [e']@(Unitₜ n₁ [ ⊢e₁ , ⊢n₁ , d₁ ] k≡k₁ prop₁) =
  Unitₜ₌ n n₁ [ ⊢e , ⊢n , d ] [ ⊢e₁ , ⊢n₁ , d₁ ]
         (≅ₜ-η-unit ⊢n ⊢n₁) (prop , prop₁)
η-unit′ {Γ = Γ} {.¹} {e} {e'} (emb 0<1 [Unit]) [e] [e'] = η-unit′ [Unit] [e] [e']

η-unit″ : ∀ {l e e'}
            ([Unit] : Γ ⊩⟨ l ⟩ Unit)
            ([e]    : Γ ⊩⟨ l ⟩ e ∷ Unit / [Unit])
            ([e']   : Γ ⊩⟨ l ⟩ e' ∷ Unit / [Unit])
          → Γ ⊩⟨ l ⟩ e ≡ e' ∷ Unit / [Unit]
η-unit″ {Γ = Γ} {l} {e} {e'} [Unit] [e] [e′] =
  irrelevanceEqTerm (Unit-intr (Unit-elim [Unit])) [Unit]
    (η-unit′ (Unit-elim [Unit])
      (irrelevanceTerm [Unit] (Unit-intr (Unit-elim [Unit])) [e])
      (irrelevanceTerm [Unit] (Unit-intr (Unit-elim [Unit])) [e′]))

-- Validity of η-unit.
η-unitᵛ : ∀ {l e e'} ([Γ] : ⊩ᵛ Γ)
  ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ])
  ([e] : Γ ⊩ᵛ⟨ l ⟩ e ∷ Unit / [Γ] / [Unit])
  ([e'] : Γ ⊩ᵛ⟨ l ⟩ e' ∷ Unit / [Γ] / [Unit])
  → Γ ⊩ᵛ⟨ l ⟩ e ≡ e' ∷ Unit / [Γ] / [Unit]
η-unitᵛ {Γ = Γ} {l} {e} {e'} [Γ] [Unit] [e] [e'] {Δ = Δ} {σ} ⊢Δ [σ] =
  let J = proj₁ ([Unit] ⊢Δ [σ])
      UnitJ : Δ ⊩⟨ l ⟩ Unit
      UnitJ = Unitᵣ (idRed:*: (Unitⱼ ⊢Δ))
      [σe] = irrelevanceTerm J UnitJ (proj₁ ([e] ⊢Δ [σ]))
      [σe'] = irrelevanceTerm J UnitJ (proj₁ ([e'] ⊢Δ [σ]))
  in  irrelevanceEqTerm UnitJ J (η-unit″ UnitJ [σe] [σe'])
