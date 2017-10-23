{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Reducibility {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties

open import Tools.Product


-- Valid types are reducible.
reducible : ∀ {A Γ l}
            ([Γ] : ⊩ᵛ Γ)
          → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
          → Γ ⊩⟨ l ⟩ A
reducible [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ [id]))

-- Valid type equality is reducible.
reducibleEq : ∀ {A B Γ l}
              ([Γ] : ⊩ᵛ Γ)
              ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
            → Γ ⊩⟨ l ⟩ A ≡ B / reducible [Γ] [A]
reducibleEq {A = A} [Γ] [A] [A≡B] =
  let [σA] = reducible {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEq″ (subst-id _) (subst-id _)
                      (proj₁ ([A] ⊢Γ [id])) [σA] ([A≡B] ⊢Γ [id])

-- Valid terms are reducible.
reducibleTerm : ∀ {t A Γ l}
                ([Γ] : ⊩ᵛ Γ)
                ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A / reducible [Γ] [A]
reducibleTerm {A = A} [Γ] [A] [t] =
  let [σA] = reducible {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceTerm″ (subst-id _) (subst-id _)
                        (proj₁ ([A] ⊢Γ [id])) [σA] (proj₁ ([t] ⊢Γ [id]))

-- Valid term equality is reducible.
reducibleEqTerm : ∀ {t u A Γ l}
                ([Γ] : ⊩ᵛ Γ)
                ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]
              → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / reducible [Γ] [A]
reducibleEqTerm {A = A} [Γ] [A] [t≡u] =
  let [σA] = reducible {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEqTerm″ (subst-id _) (subst-id _) (subst-id _)
                          (proj₁ ([A] ⊢Γ [id])) [σA] ([t≡u] ⊢Γ [id])
