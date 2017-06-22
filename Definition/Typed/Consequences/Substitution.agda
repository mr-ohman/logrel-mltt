{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Substitution where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Typed.Weakening as T
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE


_⊢ₛ_∷_ : (Δ : Con Term) (σ : Subst) (Γ : Con Term) → Set
Δ ⊢ₛ σ ∷ ε = ⊤
Δ ⊢ₛ σ ∷ (Γ ∙ A) = Δ ⊢ₛ tail σ ∷ Γ × Δ ⊢ head σ ∷ subst (tail σ) A

wellformedSubst : ∀ {Γ Δ σ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ
      → Δ ⊢ₛ σ ∷ Γ
wellformedSubst ε ⊢Δ [σ] = tt
wellformedSubst ([Γ] ∙ [A]) ⊢Δ ([tailσ] , [headσ]) =
  wellformedSubst [Γ] ⊢Δ [tailσ] , wellformedTerm (proj₁ ([A] ⊢Δ [tailσ])) [headσ]

fundamentalSubst : ∀ {Γ Δ σ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ₛ σ ∷ Γ
      → ∃ λ [Γ] → _⊩ₛ_∷_/_/_ {{eqRelInstance}} Δ σ Γ [Γ] ⊢Δ
fundamentalSubst ε ⊢Δ [σ] = ε , [σ]
fundamentalSubst (⊢Γ ∙ ⊢A) ⊢Δ ([tailσ] , [headσ]) =
  let [Γ] , [A] = fundamental ⊢A
      [Δ] , [A]' , [t] = fundamentalTerm [headσ]
      [Γ]' , [σ] = fundamentalSubst ⊢Γ ⊢Δ [tailσ]
      [tailσ]' = S.irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ]
      [idA]  = proj₁ ([A]' (soundContext [Δ]) (idSubstS [Δ]))
      [idA]' = proj₁ ([A] ⊢Δ [tailσ]')
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
  in  [Γ] ∙ [A] , ([tailσ]'
  ,   irrelevanceTerm'' (subst-id _) (subst-id _) [idA] [idA]' [idt])

irrelevanceSubst : ∀ {Γ Δ σ}
                   (⊢Γ : ⊢ Γ) (⊢Γ' : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ' : ⊢ Δ)
                 → Δ ⊢ₛ σ ∷ Γ → Δ ⊢ₛ σ ∷ Γ
irrelevanceSubst ε ε ⊢Δ ⊢Δ' σ = σ
irrelevanceSubst (⊢Γ ∙ x) (⊢Γ' ∙ x₁) ⊢Δ ⊢Δ' (tailσ , headσ) =
  let tailσ' = irrelevanceSubst ⊢Γ ⊢Γ' ⊢Δ ⊢Δ' tailσ
  in  tailσ' , headσ

substitution : ∀ {A Γ Δ σ} → Γ ⊢ A → Δ ⊢ₛ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A
substitution A σ ⊢Δ with fundamental A | fundamentalSubst (wf A) ⊢Δ σ
substitution A σ ⊢Δ | [Γ] , [A] | [Γ]' , [σ] =
  wellformed (proj₁ ([A] ⊢Δ (S.irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ])))

substitutionEq : ∀ {A B Γ Δ σ}
               → Γ ⊢ A ≡ B → Δ ⊢ₛ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A ≡ subst σ B
substitutionEq A≡B σ ⊢Δ with fundamentalEq A≡B | fundamentalSubst (wfEq A≡B) ⊢Δ σ
substitutionEq A≡B σ ⊢Δ | [Γ] , [A] , [B] , [A≡B] | [Γ]' , [σ] =
  let [σ]' = S.irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ]
  in  wellformedEq (proj₁ ([A] ⊢Δ [σ]')) ([A≡B] ⊢Δ [σ]')

substitutionTerm : ∀ {t A Γ Δ σ}
               → Γ ⊢ t ∷ A → Δ ⊢ₛ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ t ∷ subst σ A
substitutionTerm t σ ⊢Δ with fundamentalTerm t | fundamentalSubst (wfTerm t) ⊢Δ σ
substitutionTerm t σ ⊢Δ | [Γ] , [A] , [t] | [Γ]' , [σ] =
  let [σ]' = S.irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ]
  in  wellformedTerm (proj₁ ([A] ⊢Δ [σ]')) (proj₁ ([t] ⊢Δ [σ]'))

wkSubst' : ∀ {ρ σ Γ Δ Δ'} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ' : ⊢ Δ')
           ([ρ] : ρ ∷ Δ ⊆ Δ')
           ([σ] : Δ ⊢ₛ σ ∷ Γ)
         → Δ' ⊢ₛ ρ •ₛ σ ∷ Γ
wkSubst' ⊢Γ ⊢Δ ⊢Δ' ρ σ with fundamentalSubst ⊢Γ ⊢Δ σ
... | [Γ] , [σ] = wellformedSubst [Γ] ⊢Δ' (wkSubstS [Γ] ⊢Δ ⊢Δ' ρ [σ])

wk1Subst' : ∀ {F σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊢ₛ σ ∷ Γ)
          → (Δ ∙ F) ⊢ₛ wk1Subst σ ∷ Γ
wk1Subst' {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  wkSubst' ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (T.step T.id) [σ]

liftSubst' : ∀ {F σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
             (⊢F  : Γ ⊢ F)
             ([σ] : Δ ⊢ₛ σ ∷ Γ)
           → (Δ ∙ subst σ F) ⊢ₛ liftSubst σ ∷ Γ ∙ F
liftSubst' {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  let ⊢Δ∙F = ⊢Δ ∙ substitution ⊢F [σ] ⊢Δ
  in  wkSubst' ⊢Γ ⊢Δ ⊢Δ∙F (T.step T.id) [σ]
  ,   var ⊢Δ∙F (PE.subst (λ x → 0 ∷ x ∈ (Δ ∙ subst σ F))
                         (wk-subst F) here)
