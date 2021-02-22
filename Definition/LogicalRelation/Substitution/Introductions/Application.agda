{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Application {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Application of valid terms.
appᵛ : ∀ {F G t u l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ▹ G / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Π F ▹ G / [Γ] / [ΠFG])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F / [Γ] / [F])
     → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ∷ G [ u ] / [Γ] / substSΠ {F = F} {G} {u} BΠ [Γ] [F] [ΠFG] [u]
appᵛ {F = F} {G} {t} {u} [Γ] [F] [ΠFG] [t] [u] {σ = σ} ⊢Δ [σ] =
  let [G[u]] = substSΠ {F = F} {G} {u} BΠ [Γ] [F] [ΠFG] [u]
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σG[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      [σG[u]]′ = irrelevance′ (singleSubstLift G u) [σG[u]]
  in  irrelevanceTerm′ (PE.sym (singleSubstLift G u))
                       [σG[u]]′ [σG[u]]
                       (appTerm [σF] [σG[u]]′ [σΠFG] [σt] [σu])
  ,   (λ [σ′] [σ≡σ′] →
         let [σu′] = convTerm₂ [σF] (proj₁ ([F] ⊢Δ [σ′]))
                               (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
                               (proj₁ ([u] ⊢Δ [σ′]))
         in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G u))
                                [σG[u]]′ [σG[u]]
                                (app-congTerm [σF] [σG[u]]′ [σΠFG]
                                              (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                              [σu] [σu′]
                                              (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′])))

-- Application congruence of valid terms.
app-congᵛ : ∀ {F G t u a b l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ▹ G / [Γ])
            ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Π F ▹ G / [Γ] / [ΠFG])
            ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ F / [Γ] / [F])
            ([b] : Γ ⊩ᵛ⟨ l ⟩ b ∷ F / [Γ] / [F])
            ([a≡b] : Γ ⊩ᵛ⟨ l ⟩ a ≡ b ∷ F / [Γ] / [F])
          → Γ ⊩ᵛ⟨ l ⟩ t ∘ a ≡ u ∘ b ∷ G [ a ] / [Γ]
              / substSΠ {F = F} {G} {a} BΠ [Γ] [F] [ΠFG] [a]
app-congᵛ {F = F} {G} {a = a} [Γ] [F] [ΠFG] [t≡u] [a] [b] [a≡b] ⊢Δ [σ] =
  let [σF] = proj₁ ([F] ⊢Δ [σ])
      [G[a]]  = proj₁ (substSΠ {F = F} {G} {a} BΠ [Γ] [F] [ΠFG] [a] ⊢Δ [σ])
      [G[a]]′ = irrelevance′ (singleSubstLift G a) [G[a]]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σa] = proj₁ ([a] ⊢Δ [σ])
      [σb] = proj₁ ([b] ⊢Δ [σ])
  in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G a)) [G[a]]′ [G[a]]
                         (app-congTerm [σF] [G[a]]′ [σΠFG] ([t≡u] ⊢Δ [σ])
                                       [σa] [σb] ([a≡b] ⊢Δ [σ]))
