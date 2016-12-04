open import Definition.EqualityRelation

module Definition.LogicalRelation.Substitution.Weakening {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Substitution

open import Tools.Product

import Tools.PropositionalEquality as PE

wk1ₛ : ∀ {A F Γ l}
      ([Γ] : ⊩ₛ Γ)
      ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
    → Γ ⊩ₛ⟨ l ⟩ A / [Γ]
    → Γ ∙ F ⊩ₛ⟨ l ⟩ wk1 A / [Γ] ∙ [F]
wk1ₛ {A} [Γ] [F] [A] ⊢Δ [σ] =
  let [σA] = proj₁ ([A] ⊢Δ (proj₁ [σ]))
      [σA]' = irrelevance' (PE.sym (subst-wk A)) [σA]
  in  [σA]'
  ,   (λ [σ'] [σ≡σ'] →
         irrelevanceEq'' (PE.sym (subst-wk A))
                         (PE.sym (subst-wk A))
                         [σA] [σA]'
                         (proj₂ ([A] ⊢Δ (proj₁ [σ])) (proj₁ [σ']) (proj₁ [σ≡σ'])))

wk1Eqₛ : ∀ {A B F Γ l}
         ([Γ] : ⊩ₛ Γ)
         ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
         ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
         ([A≡B] : Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A])
       → Γ ∙ F ⊩ₛ⟨ l ⟩ wk1 A ≡ wk1 B / [Γ] ∙ [F] / wk1ₛ {A} {F} [Γ] [F] [A]
wk1Eqₛ {A} {B} [Γ] [F] [A] [A≡B] ⊢Δ [σ] =
  let [σA] = proj₁ ([A] ⊢Δ (proj₁ [σ]))
      [σA]' = irrelevance' (PE.sym (subst-wk A)) [σA]
  in  irrelevanceEq'' (PE.sym (subst-wk A))
                      (PE.sym (subst-wk B))
                      [σA] [σA]'
                      ([A≡B] ⊢Δ (proj₁ [σ]))
