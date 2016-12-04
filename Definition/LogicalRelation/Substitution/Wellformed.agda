open import Definition.EqualityRelation

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
