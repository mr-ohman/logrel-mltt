module Definition.LogicalRelation.Properties.Symmetry where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


mutual
  symEqT : ∀ {Γ A B l l'} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B} → Tactic Γ l l' A B [A] [B] → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symEqT (ℕ D D₁) A≡B = red D
  symEqT (ne D neK D₁ neK₁) ne[ M , D' , neM , K≡M ] = ne[ _ , D , neK , trans (sym (subset* (red D₁))) (trans (subset* (red D')) (sym K≡M)) ]
  symEqT (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
    in  Π¹[ _ , _ , red D , sym A≡B
          , (λ ρ ⊢Δ → proof-irrelevanceEq' (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)) ([F]₁ ρ ⊢Δ) (symEq ([F] ρ ⊢Δ) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)) ([F≡F'] ρ ⊢Δ)))
          , (λ ρ ⊢Δ [a] → let [a]₁ = convTerm₁ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) (proof-irrelevanceEq' (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)) ([F]₁ ρ ⊢Δ) (symEq ([F] ρ ⊢Δ) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)) ([F≡F'] ρ ⊢Δ))) [a]
                          in  proof-irrelevanceEq' (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkLiftₜ ρ x [ _ ]) G₁≡G' ([G]₁ ρ ⊢Δ [a])) ([G]₁ ρ ⊢Δ [a]) (symEq ([G] ρ ⊢Δ [a]₁) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkLiftₜ ρ x [ _ ]) G₁≡G' ([G]₁ ρ ⊢Δ [a])) ([G≡G'] ρ ⊢Δ [a]₁))) ]
  symEqT (U ⊢Γ ⊢Γ₁) A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  symEq : ∀ {Γ A B l l'} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B
