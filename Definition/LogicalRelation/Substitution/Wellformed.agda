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


wellformedₛ : ∀ {A l Γ} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ⟨ l ⟩ A / [Γ] → Γ ⊢ A
wellformedₛ [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
  in  wellformed (irrelevance' (idSubst-lemma₀ _) (proj₁ ([A] ⊢Γ idSubst)))

wellformedEqₛ : ∀ {A B l Γ} ([Γ] : ⊩ₛ Γ) ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A] → Γ ⊢ A ≅ B
wellformedEqₛ [Γ] [A] [A≡B] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]' = irrelevance' (idSubst-lemma₀ _) [idA]
  in  wellformedEq [idA]' (irrelevanceEq'' (idSubst-lemma₀ _) (idSubst-lemma₀ _)
                                           [idA] [idA]' ([A≡B] ⊢Γ idSubst))

wellformedTermₛ : ∀ {t A l Γ} ([Γ] : ⊩ₛ Γ) ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
               → Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A] → Γ ⊢ t ∷ A
wellformedTermₛ [Γ] [A] [t] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]' = irrelevance' (idSubst-lemma₀ _) (proj₁ ([A] ⊢Γ idSubst))
  in  wellformedTerm [idA]'
                    (irrelevanceTerm'' (idSubst-lemma₀ _) (idSubst-lemma₀ _)
                                       [idA] [idA]' (proj₁ ([t] ⊢Γ idSubst)))

wellformedEqTermₛ : ∀ {t u A l Γ} ([Γ] : ⊩ₛ Γ) ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
               → Γ ⊩ₛ⟨ l ⟩t' t ≡ u ∷ A / [Γ] / [A] → Γ ⊢ t ≅ u ∷ A
wellformedEqTermₛ [Γ] [A] [t≡u] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]' = irrelevance' (idSubst-lemma₀ _) (proj₁ ([A] ⊢Γ idSubst))
  in  wellformedTermEq [idA]'
                       (irrelevanceEqTerm'' (idSubst-lemma₀ _) (idSubst-lemma₀ _)
                                            (idSubst-lemma₀ _)
                                            [idA] [idA]' ([t≡u] ⊢Γ idSubst))
