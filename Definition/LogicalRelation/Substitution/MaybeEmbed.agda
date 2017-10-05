{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.MaybeEmbed {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product


-- Any level can be embedded into the highest level (validity variant).
maybeEmbₛ : ∀ {l A Γ}
            ([Γ] : ⊩ₛ Γ)
          → Γ ⊩ₛ⟨ l ⟩ A / [Γ]
          → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]
maybeEmbₛ {⁰} [Γ] [A] ⊢Δ [σ] =
  let [σA]  = proj₁ ([A] ⊢Δ [σ])
      [σA]′ = maybeEmb (proj₁ ([A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
maybeEmbₛ {¹} [Γ] [A] = [A]

-- The lowest level can be embedded in any level (validity variant).
maybeEmbₛ′ : ∀ {l A Γ}
             ([Γ] : ⊩ₛ Γ)
           → Γ ⊩ₛ⟨ ⁰ ⟩ A / [Γ]
           → Γ ⊩ₛ⟨ l ⟩ A / [Γ]
maybeEmbₛ′ {⁰} [Γ] [A] = [A]
maybeEmbₛ′ {¹} [Γ] [A] ⊢Δ [σ] =
  let [σA]  = proj₁ ([A] ⊢Δ [σ])
      [σA]′ = maybeEmb′ (proj₁ ([A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
