{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Substitution where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
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


_⊢ₛ_∷_/_/_ : (Δ : Con Term) (σ : Subst) (Γ : Con Term)
           → ⊢ Γ → ⊢ Δ → Set
Δ ⊢ₛ σ ∷ .ε / ε / ⊢Δ = ⊤
Δ ⊢ₛ σ ∷ .(Γ ∙ A) / _∙_ {Γ} {A} ⊢Γ ⊢A / ⊢Δ =
  Δ ⊢ₛ tail σ ∷ Γ / ⊢Γ / ⊢Δ × Δ ⊢ head σ ∷ subst (tail σ) A

record _⊢ₛ_∷_ (Δ : Con Term) (σ : Subst) (Γ : Con Term) : Set where
  constructor [_,_,_]
  field
    ⊢Γ  : ⊢ Γ
    ⊢Δ  : ⊢ Δ
    [σ] : Δ ⊢ₛ σ ∷ Γ / ⊢Γ / ⊢Δ

wellformedSubst : ∀ {Γ Δ σ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ
      → ∃ λ ⊢Γ → Δ ⊢ₛ σ ∷ Γ / ⊢Γ / ⊢Δ
wellformedSubst ε ⊢Δ [σ] = ε , [σ]
wellformedSubst ([Γ] ∙ [A]) ⊢Δ ([tailσ] , [headσ]) =
  let ⊢Γ , [tailσ]' = wellformedSubst [Γ] ⊢Δ [tailσ]
      [A]' = irrelevance' (subst-id _)
                          (proj₁ ([A] (soundContext [Γ]) (idSubstS [Γ])))
  in  ⊢Γ ∙ wellformed [A]'
  ,   ([tailσ]' , wellformedTerm (proj₁ ([A] ⊢Δ [tailσ])) [headσ])

fundamentalSubst : ∀ {Γ Δ σ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ₛ σ ∷ Γ / ⊢Γ / ⊢Δ
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
                 → Δ ⊢ₛ σ ∷ Γ / ⊢Γ / ⊢Δ → Δ ⊢ₛ σ ∷ Γ / ⊢Γ' / ⊢Δ'
irrelevanceSubst ε ε ⊢Δ ⊢Δ' σ = σ
irrelevanceSubst (⊢Γ ∙ x) (⊢Γ' ∙ x₁) ⊢Δ ⊢Δ' (tailσ , headσ) =
  let tailσ' = irrelevanceSubst ⊢Γ ⊢Γ' ⊢Δ ⊢Δ' tailσ
  in  tailσ' , headσ

substitution : ∀ {A Γ Δ σ} → Γ ⊢ A → Δ ⊢ₛ σ ∷ Γ → Δ ⊢ subst σ A
substitution A [ ⊢Γ , ⊢Δ , σ ] with fundamental A | fundamentalSubst ⊢Γ ⊢Δ σ
substitution A [ ⊢Γ , ⊢Δ , σ ] | [Γ] , [A] | [Γ]' , [σ] =
  wellformed (proj₁ ([A] ⊢Δ (S.irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ])))

substitutionEq : ∀ {A B Γ Δ σ}
               → Γ ⊢ A ≡ B → Δ ⊢ₛ σ ∷ Γ → Δ ⊢ subst σ A ≡ subst σ B
substitutionEq A≡B [ ⊢Γ , ⊢Δ , σ ] with fundamentalEq A≡B | fundamentalSubst ⊢Γ ⊢Δ σ
substitutionEq A≡B [ ⊢Γ , ⊢Δ , σ ] | [Γ] , [A] , [B] , [A≡B] | [Γ]' , [σ] =
  let [σ]' = S.irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ]
  in  wellformedEq (proj₁ ([A] ⊢Δ [σ]')) ([A≡B] ⊢Δ [σ]')

substitutionTerm : ∀ {t A Γ Δ σ}
               → Γ ⊢ t ∷ A → Δ ⊢ₛ σ ∷ Γ → Δ ⊢ subst σ t ∷ subst σ A
substitutionTerm t [ ⊢Γ , ⊢Δ , σ ] with fundamentalTerm t | fundamentalSubst ⊢Γ ⊢Δ σ
substitutionTerm t [ ⊢Γ , ⊢Δ , σ ] | [Γ] , [A] , [t] | [Γ]' , [σ] =
  let [σ]' = S.irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ]
  in  wellformedTerm (proj₁ ([A] ⊢Δ [σ]')) (proj₁ ([t] ⊢Δ [σ]'))

wkSubst' : ∀ {ρ σ Γ Δ Δ'} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ' : ⊢ Δ')
           ([ρ] : ρ ∷ Δ ⊆ Δ')
           ([σ] : Δ ⊢ₛ σ ∷ Γ / ⊢Γ / ⊢Δ)
         → Δ' ⊢ₛ ρ •ₛ σ ∷ Γ / ⊢Γ / ⊢Δ'
wkSubst' ⊢Γ ⊢Δ ⊢Δ' ρ σ with fundamentalSubst ⊢Γ ⊢Δ σ
... | [Γ] , [σ] =
  let q , w = wellformedSubst [Γ] ⊢Δ' (wkSubstS [Γ] ⊢Δ ⊢Δ' ρ [σ])
  in  irrelevanceSubst q ⊢Γ ⊢Δ' ⊢Δ' w

wk1Subst' : ∀ {F σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊢ₛ σ ∷ Γ / ⊢Γ / ⊢Δ)
          → (Δ ∙ F) ⊢ₛ wk1Subst σ ∷ Γ / ⊢Γ
                            / (⊢Δ ∙ ⊢F)
wk1Subst' {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  wkSubst' ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (T.step T.id) [σ]

liftSubst' : ∀ {F σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
             (⊢F  : Γ ⊢ F)
             ([σ] : Δ ⊢ₛ σ ∷ Γ / ⊢Γ / ⊢Δ)
           → (Δ ∙ subst σ F) ⊢ₛ liftSubst σ ∷ Γ ∙ F / ⊢Γ ∙ ⊢F
                             / (⊢Δ ∙ substitution ⊢F ([ ⊢Γ , ⊢Δ , [σ] ]))
liftSubst' {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  let ⊢Δ∙F = ⊢Δ ∙ substitution ⊢F ([ ⊢Γ , ⊢Δ , [σ] ])
  in  wkSubst' ⊢Γ ⊢Δ ⊢Δ∙F (T.step T.id) [σ]
  ,   var ⊢Δ∙F (PE.subst (λ x → 0 ∷ x ∈ (Δ ∙ subst σ F))
                         (wk-subst F) here)
