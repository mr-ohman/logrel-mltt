module Definition.LogicalRelation.Substitution.Properties where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties

open import Tools.Context

open import Data.Nat renaming (ℕ to Nat)
open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as PE

tailSubstS : ∀ {l A σ Γ Δ} (⊨Γ : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ) (⊢A : Δ ⊢ A)
           → Δ     ⊨⟨ l ⟩ σ      ∷ Γ / ⊨Γ / ⊢Δ
           → Δ ∙ A ⊨⟨ l ⟩ tail σ ∷ Γ / ⊨Γ / ⊢Δ ∙ ⊢A
tailSubstS ε ⊢Δ ⊢A [σ] = tt
tailSubstS (⊨Γ ∙ x) ⊢Δ ⊢A (proj₁ , proj₂) = tailSubstS ⊨Γ ⊢Δ ⊢A proj₁ , {!!}

mutual
  soundContext : ∀ {l Γ} → ⊨⟨ l ⟩ Γ → ⊢ Γ
  soundContext ε = ε
  soundContext (x ∙ x₁) = soundContext x ∙ soundness (PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (idSubst-lemma₀ _) (proj₁ (x₁ (soundContext x) (idSubstS x))))

  idSubstS : ∀ {l Γ} (⊨Γ : ⊨⟨ l ⟩ Γ) → Γ ⊨⟨ l ⟩ idSubst ∷ Γ / ⊨Γ / soundContext ⊨Γ
  idSubstS ε = tt
  idSubstS (⊨Γ ∙ x) = tailSubstS ⊨Γ (soundContext ⊨Γ)
                                    (soundness (PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (idSubst-lemma₀ _)
                                                         (proj₁ (x (soundContext ⊨Γ) (idSubstS ⊨Γ)))))
                                    (idSubstS ⊨Γ)
                    , {!!}

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
