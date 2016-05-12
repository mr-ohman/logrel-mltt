module Lemma.Soundness where

open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


--TODO
postulate fstRed : ∀ {Γ A B} → Γ ⊢ A ⇒* B → Γ ⊢ A
postulate fstRedTerm : ∀ {Γ A t u} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
postulate fstRedBoth : ∀ {Γ A B t u} → Γ ⊢ A ⇒* B → Γ ⊢ t ⇒* u ∷ B → Γ ⊢ t ∷ A

postulate fstRedEq : ∀ {Γ A B t u} → Γ ⊢ A ⇒* B → Γ ⊢ t ≡ u ∷ B → Γ ⊢ t ≡ u ∷ A

soundness : ∀ {Γ A} T → ⊢ Γ → Γ ⊩⟨ T ⟩ A → Γ ⊢ A
soundness ⁰ ⊢Γ (ℕ x) = fstRed x
soundness ⁰ ⊢Γ (ne x x₁ x₂) = fstRed x
soundness ⁰ ⊢Γ (Π x x₁ x₂ [F] [G] x₃) = fstRed x
soundness ¹ ⊢Γ U = U ⊢Γ
soundness ¹ ⊢Γ ℕ = ℕ ⊢Γ
soundness ¹ ⊢Γ (Π x x₁ A [F] [G] x₂) = Π x ▹ x₁
soundness ¹ ⊢Γ (emb x) = soundness ⁰ ⊢Γ x

soundnessEq : ∀ {Γ A B} T → ⊢ Γ → ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ A ≡ B / [A] → Γ ⊢ A ≡ B
soundnessEq ⁰ ⊢Γ (ℕ x) x₁ = trans (subset* x) (sym (subset* x₁))
soundnessEq ⁰ ⊢Γ (ne x x₁ x₂) (proj₁ , proj₂ , proj₃ , proj₄ , proj₅) = trans (subset* x) (trans proj₅ (sym (subset* proj₂)))
soundnessEq ⁰ ⊢Γ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂ , proj₃ , proj₄) = proj₃
soundnessEq ¹ ⊢Γ U x = PE.subst (λ x → _ ⊢ _ ≡ x) (PE.sym x) (refl (U ⊢Γ))
soundnessEq ¹ ⊢Γ ℕ x = PE.subst (λ x → _ ⊢ _ ≡ x) (PE.sym x) (refl (ℕ ⊢Γ))
soundnessEq ¹ ⊢Γ (Π x x₁ [A] [F] [G] x₂) (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆) =
  PE.subst (λ x → _ ⊢ _ ≡ x) (PE.trans proj₃ (PE.sym proj₄)) (refl (Π x ▹ x₁))
soundnessEq ¹ ⊢Γ (emb x) x₁ = soundnessEq ⁰ ⊢Γ x x₁

soundnessTerm : ∀ {Γ A t} T → ⊢ Γ → ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ∷ A / [A] → Γ ⊢ t ∷ A
soundnessTerm ⁰ ⊢Γ (ℕ x) (proj₁ , proj₂ , proj₃) = fstRedBoth x proj₂
soundnessTerm ⁰ ⊢Γ (ne x x₁ x₂) t₁ = t₁
soundnessTerm ⁰ ⊢Γ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂) = proj₁
soundnessTerm ¹ ⊢Γ U (proj₁ , proj₂) = proj₁
soundnessTerm ¹ ⊢Γ ℕ (proj₁ , proj₂ , proj₃) = fstRedTerm proj₂
soundnessTerm ¹ ⊢Γ (Π x x₁ [A] [F] [G] x₂) (proj₁ , proj₂) = proj₁
soundnessTerm ¹ ⊢Γ (emb x) t₁ = soundnessTerm ⁰ ⊢Γ x t₁

soundnessTermEq : ∀ {Γ A t u} T → ⊢ Γ → ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ≡ u ∷ A / [A] → Γ ⊢ t ≡ u ∷ A
soundnessTermEq ⁰ ⊢Γ (ℕ x) (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆) = fstRedEq x proj₆
soundnessTermEq ⁰ ⊢Γ (ne x x₁ x₂) t≡u = t≡u
soundnessTermEq ⁰ ⊢Γ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂ , proj₃ , proj₄) = proj₃
soundnessTermEq ¹ ⊢Γ U (proj₁ , proj₂ , proj₃ , proj₄) = proj₃
soundnessTermEq ¹ ⊢Γ ℕ (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆) = proj₆
soundnessTermEq ¹ ⊢Γ (Π x x₁ [A] [F] [G] x₂) (proj₁ , proj₂ , proj₃ , proj₄) = proj₃
soundnessTermEq ¹ ⊢Γ (emb x) t≡u = soundnessTermEq ⁰ ⊢Γ x t≡u
