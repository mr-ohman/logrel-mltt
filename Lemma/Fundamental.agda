module Lemma.Fundamental where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
-- open import Definition.LogicalRelation.Properties -- unsolved metas
open import Definition.LogicalRelation.Substitution

open import Tools.Context

open import Data.Product

import Relation.Binary.PropositionalEquality as PE

postulate
  symEq : ∀ {Γ A B} l l' ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symTermEq : ∀ {Γ A} l ([A] : Γ ⊩⟨ l ⟩ A) {t u} → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊩⟨ l ⟩ u ≡ t ∷  A / [A]


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊨⟨ ¹ ⟩ Γ
  valid ε = ε
  valid (⊢Γ ∙ x) = valid ⊢Γ ∙ fundamental ⊢Γ x

  fundamental : ∀ {Γ A} (⊢Γ : ⊢ Γ) (⊢A : Γ ⊢ A) → Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ
  fundamental ⊢Γ (ℕ x) x₁ = ℕ {!!} , λ x₂ → id (ℕ {!!})
  fundamental ⊢Γ (U x) x₁ = U , λ x₂ → PE.refl
  fundamental ⊢Γ (Π A ▹ A₁) x = {!!}
  fundamental ⊢Γ (univ x) x₁ = {!!}

  fundamentalTermEq : ∀{Γ A t t'}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ≡ t' ∷ A → Γ ⊨⟨ ¹ ⟩t t ≡ t' ∷ A / valid ⊢Γ
  fundamentalTermEq ⊢Γ (refl x) = {!!}
  fundamentalTermEq ⊢Γ (sym D) with fundamentalTermEq ⊢Γ D
  fundamentalTermEq ⊢Γ (sym D) | modelsTermEq [A] [t'] [t] [t'≡t] = modelsTermEq [A] [t] [t'] λ [σ] →
      symTermEq ¹ (proj₁ ([A] [σ])) ([t'≡t] [σ])
  fundamentalTermEq ⊢Γ (trans x x₁) = {!!}
  fundamentalTermEq ⊢Γ (conv x x₁) = {!!}
  fundamentalTermEq ⊢Γ (Π-cong x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (app-cong x x₁) = {!!}
  fundamentalTermEq ⊢Γ (β-red x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (fun-ext x x₁ x₂ x₃) = {!!}
  fundamentalTermEq ⊢Γ (suc-cong x) = {!!}
  fundamentalTermEq ⊢Γ (natrec-cong x x₁ x₂ x₃) = {!!}
  fundamentalTermEq ⊢Γ (natrec-zero x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (natrec-suc x x₁ x₂ x₃) = {!!}
