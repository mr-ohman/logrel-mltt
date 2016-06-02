module Lemma.Fundamental where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution

open import Tools.Context

open import Data.Product

import Relation.Binary.PropositionalEquality as PE


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊨⟨ ¹ ⟩ Γ
  valid ε = ε
  valid (⊢Γ ∙ x) = valid ⊢Γ ∙ fundamental ⊢Γ x

  fundamental : ∀ {Γ A} (⊢Γ : ⊢ Γ) (⊢A : Γ ⊢ A) → Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ
  fundamental ⊢Γ (ℕ x) x₁ = ℕ {!!} , λ x₂ → id (ℕ {!!})
  fundamental ⊢Γ (U x) x₁ = U , λ x₂ → PE.refl
  fundamental ⊢Γ (Π A ▹ A₁) x = {!!}
  fundamental ⊢Γ (univ x) x₁ = {!!}
