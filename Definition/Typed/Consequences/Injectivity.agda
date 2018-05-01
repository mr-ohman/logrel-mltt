{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Injectivity where

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties

open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental.Reducibility

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Helper function of injectivity for specific reducible Π-types
injectivity′ : ∀ {F G H E Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
             → Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π H ▹ E / Π-intr [ΠFG]
             → Γ ⊢ F ≡ H
             × Γ ∙ F ⊢ G ≡ E
injectivity′ (noemb (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
         (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed* (red D) Πₙ)
      H≡F′ , E≡G′ = Π-PE-injectivity (whnfRed* D′ Πₙ)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]′ = irrelevance′ (PE.trans (wk-id _) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here)
                      (refl (var (⊢Γ ∙ ⊢F) here))
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]′ = PE.subst₂ (λ x y → _ ∙ y ⊩⟨ _ ⟩ x)
                       (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                       (PE.sym F≡F₁) [G]₁
      [F≡H]₁ = [F≡F′] id ⊢Γ
      [F≡H]′ = irrelevanceEq″ (PE.trans (wk-id _) (PE.sym F≡F₁))
                               (PE.trans (wk-id _) (PE.sym H≡F′))
                               [F]₁ [F]′ [F≡H]₁
      [G≡E]₁ = [G≡G′] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]′ = irrelevanceEqLift″ (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                                   (PE.trans (wkSingleSubstId _) (PE.sym E≡G′))
                                   (PE.sym F≡F₁) [G]₁ [G]′ [G≡E]₁
  in  escapeEq [F]′ [F≡H]′ , escapeEq [G]′ [G≡E]′
injectivity′ (emb 0<1 x) [ΠFG≡ΠHE] = injectivity′ x [ΠFG≡ΠHE]

-- Injectivity of Π
injectivity : ∀ {Γ F G H E} → Γ ⊢ Π F ▹ G ≡ Π H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E
injectivity ⊢ΠFG≡ΠHE =
  let [ΠFG] , _ , [ΠFG≡ΠHE] = reducibleEq ⊢ΠFG≡ΠHE
  in  injectivity′ (Π-elim [ΠFG])
                   (irrelevanceEq [ΠFG] (Π-intr (Π-elim [ΠFG])) [ΠFG≡ΠHE])
