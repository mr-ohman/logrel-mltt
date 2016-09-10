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


lemma2 : ∀ {σ t G} → subst (consSubst (\ n → σ (suc n)) (subst (tail σ) t)) G
               PE.≡ subst σ (subst (consSubst (λ x → var (suc x)) (wk1 t)) G)
lemma2 {t = t} {G = G} = PE.trans (substEq (\ { zero → PE.sym (subst-wk t) ; (suc x) → PE.refl }) G)  (PE.sym (substCompEq G))

lemma3 : ∀ {G t σ} →
         subst (consSubst (λ n → σ (suc n)) (subst σ t)) G PE.≡
         subst σ (subst (consSubst (λ x → var (suc x)) t) G)
lemma3 {G} {t} {σ} = PE.trans (substEq (\ { zero → PE.refl ; (suc x) → PE.refl }) G)  (PE.sym (substCompEq G))

subst↑S : ∀ {F G t Γ} ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
          ([t] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t t ∷ wk1 F / [Γ] ∙ [F] / wk1ₛ {F} {F} [Γ] [F] [F])
        → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G [ t ]↑ / [Γ] ∙ [F]
subst↑S {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let [wk1F] = wk1ₛ {F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ ([wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]' = proj₁ ([F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]' = irrelevanceTerm' (subst-wk F) [σwk1F] [σwk1F]' (proj₁ ([t] ⊢Δ [σ]))
      G[t] = proj₁ ([G] {σ = consSubst (tail σ) (subst σ t)} ⊢Δ
                               (proj₁ [σ] , [t]'))
      G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (lemma3 {G} {t} {σ}) G[t]
  in  G[t]'
  ,   (λ {σ'} [σ'] [σ≡σ'] →
         let [σ't] = irrelevanceTerm' (subst-wk F) (proj₁ ([wk1F] {σ = σ'} ⊢Δ [σ'])) (proj₁ ([F] {σ = tail σ'} ⊢Δ (proj₁ [σ']))) (proj₁ ([t] ⊢Δ [σ']))
             [σt≡σ't] = irrelevanceEqTerm' (subst-wk F) [σwk1F] [σwk1F]'
                                           (proj₂ ([t] ⊢Δ [σ]) {σ' = σ'} [σ'] [σ≡σ'])
             [σG[t]≡σ'G[t]] = proj₂ ([G] {σ = consSubst (tail σ) (subst σ t)} ⊢Δ (proj₁ [σ] , [t]')) {σ' = consSubst (tail σ') (subst σ' t)} (proj₁ [σ'] , [σ't]) (proj₁ [σ≡σ'] , [σt≡σ't])
         in irrelevanceEq'' (lemma3 {G} {t} {σ}) (lemma3 {G} {t} {σ'}) G[t] G[t]' [σG[t]≡σ'G[t]])
