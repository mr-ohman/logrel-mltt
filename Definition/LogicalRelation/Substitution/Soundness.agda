{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Soundness {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties

open import Tools.Product


-- Valid types are sound.
soundness : ∀ {A Γ l}
            ([Γ] : ⊩ₛ Γ)
          → Γ ⊩ₛ⟨ l ⟩ A / [Γ]
          → Γ ⊩⟨ l ⟩ A
soundness [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ [id]))

-- Valid type equality is sound.
soundnessEq : ∀ {A B Γ l}
              ([Γ] : ⊩ₛ Γ)
              ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
            → Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A]
            → Γ ⊩⟨ l ⟩ A ≡ B / soundness [Γ] [A]
soundnessEq {A = A} [Γ] [A] [A≡B] =
  let [σA] = soundness {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEq″ (subst-id _) (subst-id _)
                      (proj₁ ([A] ⊢Γ [id])) [σA] ([A≡B] ⊢Γ [id])

-- Valid terms are sound.
soundnessTerm : ∀ {t A Γ l}
                ([Γ] : ⊩ₛ Γ)
                ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ₛ⟨ l ⟩ t ∷ A / [Γ] / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A / soundness [Γ] [A]
soundnessTerm {A = A} [Γ] [A] [t] =
  let [σA] = soundness {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceTerm″ (subst-id _) (subst-id _)
                        (proj₁ ([A] ⊢Γ [id])) [σA] (proj₁ ([t] ⊢Γ [id]))

-- Valid term equality is sound.
soundnessEqTerm : ∀ {t u A Γ l}
                ([Γ] : ⊩ₛ Γ)
                ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ₛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]
              → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / soundness [Γ] [A]
soundnessEqTerm {A = A} [Γ] [A] [t≡u] =
  let [σA] = soundness {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEqTerm″ (subst-id _) (subst-id _) (subst-id _)
                          (proj₁ ([A] ⊢Γ [id])) [σA] ([t≡u] ⊢Γ [id])
