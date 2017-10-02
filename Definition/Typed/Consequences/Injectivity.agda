{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Injectivity where

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties

open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps

open import Definition.Typed.EqRelInstance

open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.EqView
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Soundness
open import Definition.LogicalRelation.Substitution.Wellformed
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Fundamental

open import Tools.Empty
open import Tools.Unit
open import Tools.Nat
open import Tools.Product

import Tools.PropositionalEquality as PE


injectivity'' : ∀ {F G H E Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
             → Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π H ▹ E / Π-intr [ΠFG]
             → Γ ⊢ F ≡ H
             × Γ ∙ F ⊢ G ≡ E
injectivity'' (noemb (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext))
         (Π₌ F' G' D' A≡B [F≡F'] [G≡G']) =
  let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed* (red D) Π)
      H≡F' , E≡G' = Π-PE-injectivity (whnfRed* D' Π)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]' = irrelevance' (PE.trans (wk-id _) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var zero) (var (⊢Γ ∙ ⊢F) here)
                      (refl (var (⊢Γ ∙ ⊢F) here))
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]' = PE.subst₂ (λ x y → _ ∙ y ⊩⟨ _ ⟩ x)
                       (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                       (PE.sym F≡F₁) [G]₁
      [F≡H]₁ = [F≡F'] id ⊢Γ
      [F≡H]' = irrelevanceEq'' (PE.trans (wk-id _) (PE.sym F≡F₁))
                               (PE.trans (wk-id _) (PE.sym H≡F'))
                               [F]₁ [F]' [F≡H]₁
      [G≡E]₁ = [G≡G'] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]' = irrelevanceEqLift'' (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                                   (PE.trans (wkSingleSubstId _) (PE.sym E≡G'))
                                   (PE.sym F≡F₁) [G]₁ [G]' [G≡E]₁
  in  wellformedEq [F]' [F≡H]' , wellformedEq [G]' [G≡E]'
injectivity'' (emb 0<1 x) [ΠFG≡ΠHE] = injectivity'' x [ΠFG≡ΠHE]

injectivity' : ∀ {F G H E Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
             → Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π H ▹ E / [ΠFG]
             → Γ ⊢ F ≡ H
             × Γ ∙ F ⊢ G ≡ E
injectivity' [ΠFG] [ΠFG≡ΠHE] =
  injectivity'' (Π-elim [ΠFG]) (irrelevanceEq [ΠFG] (Π-intr (Π-elim [ΠFG])) [ΠFG≡ΠHE])

injectivity : ∀ {Γ F G H E} → Γ ⊢ Π F ▹ G ≡ Π H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E
injectivity ⊢ΠFG≡ΠHE with fundamentalEq ⊢ΠFG≡ΠHE
injectivity {Γ} {F} {G} {H} {E} ⊢ΠFG≡ΠHE | [Γ] , [ΠFG] , [ΠHE] , [ΠFG≡ΠHE] =
  let [ΠFG]' = soundness [Γ] [ΠFG]
      [ΠFG≡ΠHE]' = soundnessEq {Π F ▹ G} {Π H ▹ E} [Γ] [ΠFG] [ΠFG≡ΠHE]
  in  injectivity' [ΠFG]' [ΠFG≡ΠHE]'
