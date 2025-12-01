{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

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

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Helper function of injectivity for specific reducible Π-types
injectivity′ : ∀ {F G H E l} W
               ([WFG] : Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G)
             → Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ H ▹ E / B-intr W [WFG]
             → Γ ⊢ F ≡ H
             × Γ ∙ F ⊢ G ≡ E
injectivity′ W (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
         (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let F≡F₁ , G≡G₁ = B-PE-injectivity W (whnfRed* (red D) ⟦ W ⟧ₙ)
      H≡F′ , E≡G′ = B-PE-injectivity W (whnfRed* D′ ⟦ W ⟧ₙ)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]′ = irrelevance′ (PE.trans (wk-id _) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var x0) (var (⊢Γ ∙ ⊢F) here)
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
injectivity′ W (emb 0<1 x) [WFG≡WHE] = injectivity′ W x [WFG≡WHE]

-- Injectivity of W
B-injectivity : ∀ {F G H E} W → Γ ⊢ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E
B-injectivity W ⊢WFG≡WHE =
  let [WFG] , _ , [WFG≡WHE] = reducibleEq ⊢WFG≡WHE
  in  injectivity′ W (B-elim W [WFG])
                   (irrelevanceEq [WFG] (B-intr W (B-elim W [WFG])) [WFG≡WHE])

injectivity : ∀ {F G H E} → Γ ⊢ Π F ▹ G ≡ Π H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E
injectivity = B-injectivity BΠ

Σ-injectivity : ∀ {F G H E} → Γ ⊢ Σ F ▹ G ≡ Σ H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E
Σ-injectivity = B-injectivity BΣ

∪-injectivity′ : ∀ {A B C D l}
                   ([AB] : Γ ⊩⟨ l ⟩∪ A ∪ B)
             → Γ ⊩⟨ l ⟩ A ∪ B ≡ C ∪ D / ∪-intr [AB]
             → Γ ⊢ A ≡ C
             × Γ ⊢ B ≡ D
∪-injectivity′ (noemb (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T])) (∪₌ S′ T′ D′ A≡B [S≡S′] [T≡T′]) =
  let A≡A₁ , B≡B₁ = ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
      C≡A′ , D≡B′ = ∪-PE-injectivity (whnfRed* D′ ∪ₙ)
      ⊢Γ     = wf ⊢S
      [A]₁   = [S] id ⊢Γ
      [A]′   = irrelevance′ (PE.trans (wk-id _) (PE.sym A≡A₁)) [A]₁
      [A≡C]₁ = [S≡S′] id ⊢Γ
      [A≡C]′ = irrelevanceEq″ (PE.trans (wk-id _) (PE.sym A≡A₁))
                              (PE.trans (wk-id _) (PE.sym C≡A′))
                              [A]₁ [A]′ [A≡C]₁
      [B]₁   = [T] id ⊢Γ
      [B]′   = irrelevance′ (PE.trans (wk-id _) (PE.sym B≡B₁)) [B]₁
      [B≡D]₁ = [T≡T′] id ⊢Γ
      [B≡D]′ = irrelevanceEq″ (PE.trans (wk-id _) (PE.sym B≡B₁))
                              (PE.trans (wk-id _) (PE.sym D≡B′))
                              [B]₁ [B]′ [B≡D]₁
  in  escapeEq [A]′ [A≡C]′ ,
      escapeEq [B]′ [B≡D]′
∪-injectivity′ (emb 0<1 [AB]) ⊢AB = ∪-injectivity′ [AB] ⊢AB

∪-injectivity : ∀ {A B C D} → Γ ⊢ A ∪ B ≡ C ∪ D → Γ ⊢ A ≡ C × Γ ⊢ B ≡ D
∪-injectivity ⊢AB≡CD =
  let [AB] , _ , [AB≡CD] = reducibleEq ⊢AB≡CD
  in  ∪-injectivity′ (∪-elim [AB])
                     (irrelevanceEq [AB] (∪-intr (∪-elim [AB])) [AB≡CD])

∥-injectivity′ : ∀ {A C l}
                   ([∥A∥] : Γ ⊩⟨ l ⟩∥ ∥ A ∥)
             → Γ ⊩⟨ l ⟩ ∥ A ∥ ≡ ∥ C ∥ / ∥-intr [∥A∥]
             → Γ ⊢ A ≡ C
∥-injectivity′ (noemb (∥ᵣ S D ⊢S A≡A [S])) (∥₌ S′ D′ A≡B [S≡S′]) =
  let A≡A₁ = ∥-PE-injectivity (whnfRed* (red D) ∥ₙ)
      C≡A′ = ∥-PE-injectivity (whnfRed* D′ ∥ₙ)
      ⊢Γ     = wf ⊢S
      [A]₁   = [S] id ⊢Γ
      [A]′   = irrelevance′ (PE.trans (wk-id _) (PE.sym A≡A₁)) [A]₁
      [A≡C]₁ = [S≡S′] id ⊢Γ
      [A≡C]′ = irrelevanceEq″ (PE.trans (wk-id _) (PE.sym A≡A₁))
                              (PE.trans (wk-id _) (PE.sym C≡A′))
                              [A]₁ [A]′ [A≡C]₁
  in  escapeEq [A]′ [A≡C]′
∥-injectivity′ (emb 0<1 [A]) ⊢A = ∥-injectivity′ [A] ⊢A

∥-injectivity : ∀ {A C} → Γ ⊢ ∥ A ∥ ≡ ∥ C ∥ → Γ ⊢ A ≡ C
∥-injectivity ⊢A≡C =
  let [A] , _ , [A≡C] = reducibleEq ⊢A≡C
  in  ∥-injectivity′ (∥-elim [A])
                     (irrelevanceEq [A] (∥-intr (∥-elim [A])) [A≡C])
