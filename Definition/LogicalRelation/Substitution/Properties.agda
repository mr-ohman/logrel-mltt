module Definition.LogicalRelation.Substitution.Properties where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Weakening as LR

open import Tools.Context

open import Data.Nat renaming (ℕ to Nat)
open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as PE


todoPrf : ∀ σ F → wk1 (subst σ F) PE.≡ subst (tail (liftSubst σ)) F
todoPrf σ F = PE.trans (wk-subst F) PE.refl

todoPrf₁ : ∀ σ → wk1Subst σ PE.≡ tail (liftSubst σ)
todoPrf₁ σ = PE.refl

todoPrfL₃ : ∀ σ F → subst (liftSubst (tail (wk1Subst σ))) F PE.≡
      subst (liftSubst (wk1Subst (tail σ))) F
todoPrfL₃ σ U = {!!}
todoPrfL₃ σ (Π F ▹ F₁) = {!!}
todoPrfL₃ σ ℕ = {!!}
todoPrfL₃ σ (var x) = PE.refl
todoPrfL₃ σ (lam F) = {!!}
todoPrfL₃ σ (F ∘ F₁) = {!!}
todoPrfL₃ σ zero = {!!}
todoPrfL₃ σ (suc F) = {!!}
todoPrfL₃ σ (natrec F F₁ F₂ F₃) = {!!}

todoPrf₃ : ∀ σ F → subst (tail (wk1Subst σ)) F PE.≡ subst (wk1Subst (tail σ)) F
todoPrf₃ σ U = {!!}
todoPrf₃ σ (Π F ▹ F₁) = {!!}
todoPrf₃ σ ℕ = {!!}
todoPrf₃ σ (var x) = PE.refl
todoPrf₃ σ (lam F) = PE.cong lam {!!}
todoPrf₃ σ (F ∘ F₁) = {!!}
todoPrf₃ σ zero = {!!}
todoPrf₃ σ (suc F) = {!!}
todoPrf₃ σ (natrec F F₁ F₂ F₃) = {!!}

todoPrf₂ : ∀ σ F → wk1 (subst (tail σ) F) PE.≡ subst (tail (wk1Subst σ)) F
todoPrf₂ σ F = PE.trans (wk-subst F) (todoPrf₃ σ F)

postulate
  ⊆-refl : (Γ : Con Term) → Γ T.⊆ Γ
  wk-⊆-refl : ∀ Γ t → T.wkₜ (⊆-refl Γ) t PE.≡ t

consSubstS : ∀ {l σ t A Γ Δ} (⊨Γ : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ)
           ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / ⊨Γ / ⊢Δ)
           ([A] : Γ ⊨⟨ l ⟩ A / ⊨Γ)
           ([t] : Δ ⊩⟨ l ⟩ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ]))
         → Δ ⊨⟨ l ⟩ consSubst σ t ∷ Γ ∙ A / ⊨Γ ∙ [A] / ⊢Δ
consSubstS ⊨Γ ⊢Δ [σ] [A] [t] = [σ] , [t]

wkSubstS : ∀ {l σ Γ Δ Δ'} (⊨Γ : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ) (⊢Δ' : ⊢ Δ')
           (ρ : Δ T.⊆ Δ')
           ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / ⊨Γ / ⊢Δ)
         → Δ' ⊨⟨ l ⟩ wkSubst (T.toWk ρ) σ ∷ Γ / ⊨Γ / ⊢Δ'
wkSubstS ε ⊢Δ ⊢Δ' ρ [σ] = tt
wkSubstS {σ = σ} {Γ = Γ ∙ A} (⊨Γ ∙ x) ⊢Δ ⊢Δ' ρ [σ] =
  let [tailσ] = wkSubstS ⊨Γ ⊢Δ ⊢Δ' ρ (proj₁ [σ])
  in  [tailσ]
   ,  proof-irrelevanceTerm' (wk-subst A)
        (LR.wk ρ ⊢Δ' (proj₁ (x ⊢Δ (proj₁ [σ]))))
        (proj₁ (x ⊢Δ' [tailσ]))
        (LR.wkTerm ρ ⊢Δ' (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ]))

wk1SubstS : ∀ {l F σ Γ Δ} (⊨Γ : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / ⊨Γ / ⊢Δ)
          → (Δ ∙ F) ⊨⟨ l ⟩ wk1Subst σ ∷ Γ / ⊨Γ
                            / (⊢Δ ∙ ⊢F)
wk1SubstS {l} {F} {σ} {Γ} {Δ} ⊨Γ ⊢Δ ⊢F [σ] =
  PE.subst (λ x → Δ ∙ F ⊨⟨ l ⟩ x ∷ Γ / ⊨Γ / ⊢Δ ∙ ⊢F)
           {!!}
           (wkSubstS ⊨Γ ⊢Δ (⊢Δ ∙ ⊢F) (T.step (⊆-refl Δ)) [σ])

liftSubstS : ∀ {l F σ Γ Δ} (⊨Γ : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ)
             ([F] : Γ ⊨⟨ l ⟩ F / ⊨Γ)
             ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / ⊨Γ / ⊢Δ)
           → (Δ ∙ subst σ F) ⊨⟨ l ⟩ liftSubst σ ∷ Γ ∙ F / ⊨Γ ∙ [F]
                             / (⊢Δ ∙ soundness (proj₁ ([F] ⊢Δ [σ])))
liftSubstS {F = F} {σ = σ} {Δ = Δ} ⊨Γ ⊢Δ [F] [σ] =
  let ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
      [tailσ] = wk1SubstS {F = subst σ F} ⊨Γ ⊢Δ (soundness (proj₁ ([F] ⊢Δ [σ]))) [σ]
  in  [tailσ] , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [tailσ])) (var zero)
                        (var (⊢Δ ∙ ⊢F) (PE.subst (λ x → 0 ∷ x ∈ (Δ ∙ subst σ F))
                                                 (todoPrf σ F) here))

proof-irrelevanceTermΔ : ∀ {l σ Γ Δ}
                          (⊨Γ : ⊨⟨ l ⟩ Γ)
                          (⊢Δ ⊢Δ' : ⊢ Δ)
                        → Δ ⊨⟨ l ⟩ σ ∷ Γ / ⊨Γ / ⊢Δ
                        → Δ ⊨⟨ l ⟩ σ ∷ Γ / ⊨Γ / ⊢Δ'
proof-irrelevanceTermΔ ε ⊢Δ ⊢Δ' [σ] = tt
proof-irrelevanceTermΔ (⊨Γ ∙ x) ⊢Δ ⊢Δ' [σ] =
  let [tailσ] = proof-irrelevanceTermΔ ⊨Γ ⊢Δ ⊢Δ' (proj₁ [σ])
  in  [tailσ] , proof-irrelevanceTerm (proj₁ (x ⊢Δ (proj₁ [σ])))
                                      (proj₁ (x ⊢Δ' [tailσ]))
                                      (proj₂ [σ])

proof-irrelevanceTermΔ' : ∀ {l σ Γ Δ Δ'}
                          (⊨Γ : ⊨⟨ l ⟩ Γ)
                          (eq : Δ PE.≡ Δ')
                          (⊢Δ  : ⊢ Δ)
                          (⊢Δ' : ⊢ Δ')
                        → Δ  ⊨⟨ l ⟩ σ ∷ Γ / ⊨Γ / ⊢Δ
                        → Δ' ⊨⟨ l ⟩ σ ∷ Γ / ⊨Γ / ⊢Δ'
proof-irrelevanceTermΔ' ⊨Γ PE.refl ⊢Δ ⊢Δ' [σ] = proof-irrelevanceTermΔ ⊨Γ ⊢Δ ⊢Δ' [σ]

mutual
  soundContext : ∀ {l Γ} → ⊨⟨ l ⟩ Γ → ⊢ Γ
  soundContext ε = ε
  soundContext (x ∙ x₁) = soundContext x ∙ soundness (PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (idSubst-lemma₀ _) (proj₁ (x₁ (soundContext x) (idSubstS x))))

  idSubstS : ∀ {l Γ} (⊨Γ : ⊨⟨ l ⟩ Γ) → Γ ⊨⟨ l ⟩ idSubst ∷ Γ / ⊨Γ / soundContext ⊨Γ
  idSubstS ε = tt
  idSubstS {Γ = Γ ∙ A} (⊨Γ ∙ [A]) =
    let ⊢Γ = soundContext ⊨Γ
        ⊢Γ∙A = soundContext (⊨Γ ∙ [A])
        ⊢Γ∙A' = ⊢Γ ∙ soundness (proj₁ ([A] ⊢Γ (idSubstS ⊨Γ)))
        [tailσ] = proof-irrelevanceTermΔ' ⊨Γ (PE.cong (_∙_ Γ) (idSubst-lemma₀ A)) ⊢Γ∙A' ⊢Γ∙A (wk1SubstS {F = subst idSubst A} ⊨Γ ⊢Γ (soundness (proj₁ ([A] (soundContext ⊨Γ) (idSubstS ⊨Γ)))) (idSubstS ⊨Γ))
    in  [tailσ] , neuTerm (proj₁ ([A] ⊢Γ∙A [tailσ]))
                          (var zero)
                          (var ⊢Γ∙A (PE.subst (λ x → 0 ∷ x ∈ (Γ ∙ A))
                                              (todoPrf idSubst A)
                                              (PE.subst (λ x → 0 ∷ wk1 (subst idSubst A) ∈ (Γ ∙ x))
                                                        (idSubst-lemma₀ A) here)))

reflIdSubst : ∀ {l Γ} (⊨Γ : ⊨⟨ l ⟩ Γ)
            → Γ ⊨⟨ l ⟩ idSubst ≡ idSubst ∷ Γ / ⊨Γ / soundContext ⊨Γ / idSubstS ⊨Γ
reflIdSubst ε = tt
reflIdSubst (⊨Γ ∙ x) = {!!}

symS : ∀ {l σ σ' Γ Δ} (⊨Γ : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ)
       ([σ]  : Δ ⊨⟨ l ⟩ σ  ∷ Γ / ⊨Γ / ⊢Δ)
       ([σ'] : Δ ⊨⟨ l ⟩ σ' ∷ Γ / ⊨Γ / ⊢Δ)
     → Δ ⊨⟨ l ⟩ σ ≡ σ' ∷ Γ / ⊨Γ / ⊢Δ / [σ]
     → Δ ⊨⟨ l ⟩ σ' ≡ σ ∷ Γ / ⊨Γ / ⊢Δ / [σ']
symS ε ⊢Δ [σ] [σ'] [σ≡σ'] = tt
symS (⊨Γ ∙ x) ⊢Δ [σ] [σ'] [σ≡σ'] = symS ⊨Γ ⊢Δ (proj₁ [σ]) (proj₁ [σ']) (proj₁ [σ≡σ'])
  , let [σA]           = proj₁ (x ⊢Δ (proj₁ [σ]))
        [σ'A]          = proj₁ (x ⊢Δ (proj₁ [σ']))
        [σA≡σ'A]       = (proj₂ (x ⊢Δ (proj₁ [σ]))) (proj₁ [σ≡σ'])
        [headσ'≡headσ] = symEqTerm [σA] (proj₂ [σ≡σ'])
    in  convEqTerm₁ [σA] [σ'A] [σA≡σ'A] [headσ'≡headσ]

transS : ∀ {l σ σ' σ'' Γ Δ} (⊨Γ : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ)
         ([σ]   : Δ ⊨⟨ l ⟩ σ   ∷ Γ / ⊨Γ / ⊢Δ)
         ([σ']  : Δ ⊨⟨ l ⟩ σ'  ∷ Γ / ⊨Γ / ⊢Δ)
         ([σ''] : Δ ⊨⟨ l ⟩ σ'' ∷ Γ / ⊨Γ / ⊢Δ)
       → Δ ⊨⟨ l ⟩ σ  ≡ σ'  ∷ Γ / ⊨Γ / ⊢Δ / [σ]
       → Δ ⊨⟨ l ⟩ σ' ≡ σ'' ∷ Γ / ⊨Γ / ⊢Δ / [σ']
       → Δ ⊨⟨ l ⟩ σ  ≡ σ'' ∷ Γ / ⊨Γ / ⊢Δ / [σ]
transS ε ⊢Δ [σ] [σ'] [σ''] [σ≡σ'] [σ'≡σ''] = tt
transS (⊨Γ ∙ x) ⊢Δ [σ] [σ'] [σ''] [σ≡σ'] [σ'≡σ''] = transS ⊨Γ ⊢Δ (proj₁ [σ]) (proj₁ [σ']) (proj₁ [σ'']) (proj₁ [σ≡σ']) (proj₁ [σ'≡σ''])
  , let [σA]   = proj₁ (x ⊢Δ (proj₁ [σ]))
        [σ'A]  = proj₁ (x ⊢Δ (proj₁ [σ']))
        [σ''A] = proj₁ (x ⊢Δ (proj₁ [σ'']))
        [σ'≡σ'']' = convEqTerm₂ [σA] [σ'A] ((proj₂ (x ⊢Δ (proj₁ [σ]))) (proj₁ [σ≡σ'])) (proj₂ [σ'≡σ''])
    in  transEqTerm [σA] (proj₂ [σ≡σ']) [σ'≡σ'']'
