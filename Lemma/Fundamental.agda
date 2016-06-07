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
  reflTermEq : ∀ {Γ A} l ([A] : Γ ⊩⟨ l ⟩ A) {t} → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊩⟨ l ⟩ t ≡ t ∷  A / [A]
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

  fundamentalTerm : ∀{Γ A t}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ∷ A →
    ∃ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A]
  fundamentalTerm ⊢Γ (ℕ x) = {!!}
  fundamentalTerm ⊢Γ (Π x ▹ x₁) = {!!}
  fundamentalTerm ⊢Γ (var x₁ x₂) = {!!}
  fundamentalTerm ⊢Γ (lam x x₁) = {!!}
  fundamentalTerm ⊢Γ (Dt ∘ Du) with fundamentalTerm ⊢Γ Dt | fundamentalTerm ⊢Γ Du
  ... | [ΠAB] , [t] | [A] , [u] = (λ [σ] → {!!} , {!!}) , {!!}
  fundamentalTerm ⊢Γ (zero x) = {!!}
  fundamentalTerm ⊢Γ (suc x) = {!!}
  fundamentalTerm ⊢Γ (natrec x x₁ x₂ x₃) = {!!}
  fundamentalTerm ⊢Γ (conv x x₁) = {!!}

  fundamentalTermEq : ∀{Γ A t t'}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ≡ t' ∷ A → Γ ⊨⟨ ¹ ⟩t t ≡ t' ∷ A / valid ⊢Γ
  fundamentalTermEq ⊢Γ (refl D) with fundamentalTerm ⊢Γ D
  ... | [A] , [t] = modelsTermEq [A] [t] [t] λ [σ] → reflTermEq ¹ (proj₁ ([A] [σ])) (proj₁ ([t] [σ]))
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
