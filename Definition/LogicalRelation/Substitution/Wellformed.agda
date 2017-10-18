{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Wellformed {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties

open import Definition.Typed

open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties

open import Tools.Product


-- Valid types are well-formed.
wellformedᵛ : ∀ {A l Γ} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ A / [Γ] → Γ ⊢ A
wellformedᵛ [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
  in  wellformed (irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ idSubst)))

-- Valid type equality respects the equality relation.
wellformedEqᵛ : ∀ {A B l Γ} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A] → Γ ⊢ A ≅ B
wellformedEqᵛ [Γ] [A] [A≡B] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) [idA]
  in  wellformedEq [idA]′ (irrelevanceEq″ (subst-id _) (subst-id _)
                                           [idA] [idA]′ ([A≡B] ⊢Γ idSubst))

-- Valid terms are well-formed.
wellformedTermᵛ : ∀ {t A l Γ} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A] → Γ ⊢ t ∷ A
wellformedTermᵛ [Γ] [A] [t] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ idSubst))
  in  wellformedTerm [idA]′
                    (irrelevanceTerm″ (subst-id _) (subst-id _)
                                       [idA] [idA]′ (proj₁ ([t] ⊢Γ idSubst)))

-- Valid term equality respects the equality relation.
wellformedEqTermᵛ : ∀ {t u A l Γ} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A] → Γ ⊢ t ≅ u ∷ A
wellformedEqTermᵛ [Γ] [A] [t≡u] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ idSubst))
  in  wellformedTermEq [idA]′
                       (irrelevanceEqTerm″ (subst-id _) (subst-id _)
                                            (subst-id _)
                                            [idA] [idA]′ ([t≡u] ⊢Γ idSubst))
