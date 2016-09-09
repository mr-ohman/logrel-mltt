module Definition.LogicalRelation.Substitution.Introductions.Temp where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat renaming (ℕ to Nat)

import Relation.Binary.PropositionalEquality as PE

open import Definition.LogicalRelation.Substitution.Introductions


subst↑ : ∀ {F G t Γ Δ σ} ([Γ] : ⊩ₛ Γ)
         ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
         ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
         (⊢Δ : ⊢ Δ)
         ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
         ([t] : Δ ⊩⟨ ¹ ⟩ t ∷ subst σ F / proj₁ ([F] ⊢Δ [σ]))
       → Δ ⊩⟨ ¹ ⟩ subst (liftSubst σ) G [ t ]↑
subst↑ {F} {G} {t} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] [t] =
  let G[t] = proj₁ ([G] {σ = consSubst σ t} ⊢Δ
                   ([σ] , [t]))
      G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (PE.trans (substCompEq G) {!!})) G[t]
  in  G[t]'


lemma2 : ∀ {σ t G} → subst (consSubst (\ n → σ (suc n)) (subst (tail σ) t)) G
               PE.≡ subst σ (subst (consSubst (λ x → var (suc x)) (wk1 t)) G)
lemma2 {t = t} {G = G} = PE.trans (substEq (\ { zero → PE.sym (subst-wk t) ; (suc x) → PE.refl }) G)  (PE.sym (substCompEq G))

subst↑S : ∀ {F G t Γ} ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
          ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
        → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G [ wk1 t ]↑ / [Γ] ∙ [F]
subst↑S {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let G[t] = proj₁ ([G] {σ = consSubst (tail σ) (subst (tail σ) t)} ⊢Δ
                               ((proj₁ [σ]) , (proj₁ ([t] ⊢Δ (proj₁ [σ])))))
      G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (lemma2 {σ} {t} {G}) G[t]
  in  G[t]' , {!G [ t ]↑!}

lemma3 : ∀ {G t σ} →
         subst (consSubst (λ n → σ (suc n)) (subst σ t)) G PE.≡
         subst σ (subst (consSubst (λ x → var (suc x)) t) G)
lemma3 {G} {t} {σ} = PE.trans (substEq (\ { zero → PE.refl ; (suc x) → PE.refl }) G)  (PE.sym (substCompEq G))

subst↑S' : ∀ {F G t Γ} ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
          ([t] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t t ∷ wk1 F / [Γ] ∙ [F] / wk1ₛ [Γ] [F] [F])
        → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G [ t ]↑ / [Γ] ∙ [F]
subst↑S' {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let G[t] = proj₁ ([G] {σ = consSubst (tail σ) (subst σ t)} ⊢Δ
                               ((proj₁ [σ]) , (let r = (proj₁ ([t] ⊢Δ  [σ] )) in {!!} )))
      G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (lemma3 {G} {t} {σ}) G[t]
  in  G[t]' , {!G [ t ]↑!}
