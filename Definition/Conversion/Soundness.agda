{-# OPTIONS --without-K #-}

module Definition.Conversion.Soundness where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.LogicalRelation.Consequences.InverseUniv


mutual
  soundness~↑ : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑ A → Γ ⊢ k ≡ l ∷ A
  soundness~↑ (var x) = refl x
  soundness~↑ (app k~l x₁) = app-cong (soundness~↓ k~l) (soundnessConv↑Term x₁)
  soundness~↑ (natrec x₁ x₂ x₃ k~l) =
    natrec-cong (soundnessConv↑ x₁) (soundnessConv↑Term x₂)
                (soundnessConv↑Term x₃) (soundness~↓ k~l)

  soundness~↓ : ∀ {k l A Γ} → Γ ⊢ k ~ l ↓ A → Γ ⊢ k ≡ l ∷ A
  soundness~↓ ([~] A₁ D whnfA k~l) = conv (soundness~↑ k~l) (subset* D)

  soundnessConv↑ : ∀ {A B Γ} → Γ ⊢ A [conv↑] B → Γ ⊢ A ≡ B
  soundnessConv↑ ([↑] A' B' D D' whnfA' whnfB' A'<>B') =
    trans (subset* D) (trans (soundnessConv↓ A'<>B') (sym (subset* D')))

  soundnessConv↓ : ∀ {A B Γ} → Γ ⊢ A [conv↓] B → Γ ⊢ A ≡ B
  soundnessConv↓ (U-refl ⊢Γ) = refl (U ⊢Γ)
  soundnessConv↓ (ℕ-refl ⊢Γ) = refl (ℕ ⊢Γ)
  soundnessConv↓ (ne x) = univ (soundness~↑ x)
  soundnessConv↓ (Π-cong F c c₁) =
    Π-cong F (soundnessConv↑ c) (soundnessConv↑ c₁)

  soundnessConv↑Term : ∀ {a b A Γ} → Γ ⊢ a [conv↑] b ∷ A → Γ ⊢ a ≡ b ∷ A
  soundnessConv↑Term ([↑]ₜ B t' u' D d d' whnfB whnft' whnfu' t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d'))))
         (sym (subset* D))

  soundnessConv↓Term : ∀ {a b A Γ} → Γ ⊢ a [conv↓] b ∷ A → Γ ⊢ a ≡ b ∷ A
  soundnessConv↓Term (ℕ-ins x x₁) = conv (soundness~↑ x) (subset* x₁)
  soundnessConv↓Term (ne-ins x x₁ x₂) = conv (soundness~↑ x) (subset* x₁)
  soundnessConv↓Term (univ x x₁ x₂) = inverseUnivEq x (soundnessConv↑ x₂)
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zero ⊢Γ)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (fun-ext F x x₁ c) =
    fun-ext F x x₁ (soundnessConv↑Term c)
