{-# OPTIONS --without-K #-}

module Definition.LogicalRelation.Substitution.Introductions.SingleSubstInj where

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
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Product
open import Tools.Unit
open import Tools.Empty
open import Tools.Nat

import Tools.PropositionalEquality as PE


substVar0Id' : ∀ x → (purge (lift (step id)) (consSubst idSubst (var zero)))
       x
       PE.≡ idSubst x
substVar0Id' zero = PE.refl
substVar0Id' (suc x) = PE.refl

substVar0Id : ∀ F → (U.wk (lift (step id)) F) [ var zero ] PE.≡ F
substVar0Id F = PE.trans (subst-wk F) (PE.trans (substEq substVar0Id' F) (substIdEq F))

-- TODO move to own module for injectivity in first lr
injectivityΠ : ∀ {F G Γ l} → Γ ⊩⟨ l ⟩ Π F ▹ G → Γ ⊩⟨ l ⟩ F × Γ ∙ F ⊩⟨ l ⟩ G
injectivityΠ (ℕ D) = {!!}
injectivityΠ (ne D neK) = {!!}
injectivityΠ (Π D ⊢F ⊢G [F] [G] G-ext) =
  let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] T.id ⊢Γ
      [F]' = irrelevance' (PE.trans (wk-id _ zero) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (T.step T.id) (⊢Γ ∙ ⊢F)) (var zero) (var (⊢Γ ∙ ⊢F) here)
      [G]₁ = [G] (T.step T.id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]' = irrelevanceΓ' (PE.cong₂ _∙_ PE.refl (PE.sym F≡F₁))
                           (PE.trans (substVar0Id _) (PE.sym G≡G₁)) [G]₁
  in  [F]' , [G]'
injectivityΠ (emb x) = {!!}

injectivityΠEq : ∀ {F F' G G' Γ l}
               → ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
               → Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π F' ▹ G' / [ΠFG]
               → let [F] , [G] = injectivityΠ [ΠFG] in
                 Γ ⊩⟨ l ⟩ F ≡ F' / [F] × Γ ∙ F ⊩⟨ l ⟩ G ≡ G' / [G]
injectivityΠEq (ℕ D) [ΠFG≡ΠF'G'] = {!!}
injectivityΠEq (ne D neK) [ΠFG≡ΠF'G'] = {!!}
injectivityΠEq (Π D ⊢F ⊢G [F] [G] G-ext) (Π₌ F'' G'' D' A≡B [F≡F'] [G≡G']) =
  let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
      H≡F' , E≡G' = Π-PE-injectivity (whnfRed*' D' Π)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] T.id ⊢Γ
      [F]' = irrelevance' (PE.trans (wk-id _ zero) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (T.step T.id) (⊢Γ ∙ ⊢F)) (var zero) (var (⊢Γ ∙ ⊢F) here)
      [G]₁ = [G] (T.step T.id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]' = irrelevanceΓ' (PE.cong₂ _∙_ PE.refl (PE.sym F≡F₁))
                           (PE.trans (substVar0Id _) (PE.sym G≡G₁)) [G]₁
      [F≡H]₁ = [F≡F'] T.id ⊢Γ
      [F≡H]' = irrelevanceEq'' (PE.trans (wk-id _ zero) (PE.sym F≡F₁))
                               (PE.trans (wk-id _ zero) (PE.sym H≡F'))
                               [F]₁ [F]' [F≡H]₁
      [G≡E]₁ = [G≡G'] (T.step T.id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]' = irrelevanceEqLift'' (PE.trans (substVar0Id _) (PE.sym G≡G₁))
                                   (PE.trans (substVar0Id _) (PE.sym E≡G'))
                                   (PE.sym F≡F₁) [G]₁ [G]' [G≡E]₁
  in  [F≡H]' , [G≡E]'
injectivityΠEq (emb x) [ΠFG≡ΠF'G'] = {!!}

injectivityΠS : ∀ {F G Γ l} ([Γ] : ⊩ₛ Γ)
              → Γ ⊩ₛ⟨ l ⟩ Π F ▹ G / [Γ]
              → ∃ λ ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
              → Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F]
injectivityΠS [Γ] [ΠFG] =
  (λ ⊢Δ [σ] →
     let [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
         [F] , [G] = injectivityΠ [σΠFG]
     in  [F]
     ,   (λ [σ'] [σ≡σ'] → proj₁ (injectivityΠEq [σΠFG] (proj₂ ([ΠFG] ⊢Δ [σ]) [σ'] [σ≡σ']))))
  ,
  (λ ⊢Δ [σ] →
     let [σΠFG] = proj₁ ([ΠFG] ⊢Δ (proj₁ [σ]))
         [F] , [G] = injectivityΠ [σΠFG]
     in  irrelevanceΓ' {!!} {!!} (proj₂ (injectivityΠ (proj₁ ([ΠFG] ⊢Δ {!!}))))
     ,   (λ [σ'] [σ≡σ'] → proj₂ (injectivityΠEq [σΠFG] {!!})))

substSΠ' : ∀ {F G t Γ l}
          ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
          ([ΠFG] : Γ ⊩ₛ⟨ l ⟩ Π F ▹ G / [Γ])
          ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
        → Γ ⊩ₛ⟨ l ⟩ G [ t ] / [Γ]
substSΠ' {F} {G} {t} [Γ] [F] [ΠFG] [t] =
  let [F]' , [G]' = injectivityΠS [Γ] [ΠFG]
  in  substS [Γ] [F] [G]' [t]

substSΠEq' : ∀ {F G t u Γ l}
            ([Γ] : ⊩ₛ Γ)
            ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
            ([ΠFG] : Γ ⊩ₛ⟨ l ⟩ Π F ▹ G / [Γ])
            ([t]   : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
            ([u]   : Γ ⊩ₛ⟨ l ⟩t u ∷ F / [Γ] / [F])
            ([t≡u] : Γ ⊩ₛ⟨ l ⟩t' t ≡ u ∷ F / [Γ] / [F])
          → Γ ⊩ₛ⟨ l ⟩ G [ t ] ≡ G [ u ] / [Γ] / substSΠ' {F} {G} {t} [Γ] [F] [ΠFG] [t]
substSΠEq' {F} {G} {t} {u} [Γ] [F] [ΠFG] [t] [u] [t≡u] =
  let q = {!!}
  in  substSEq [Γ] [F] [F] (reflₛ [Γ] [F]) {!!} {!!} {!!} [t] [u] [t≡u]
