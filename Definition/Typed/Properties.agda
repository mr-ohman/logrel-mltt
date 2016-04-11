module Definition.Typed.Properties where

open import Data.Product

open import Tools.Context
open import Definition.Untyped
open import Definition.Typed

-- -- DO NOT HOLD IN GENERAL
-- mutual
--   weaken-⊢Γ : ∀ {Γ Δ} → Γ ⊆ Δ → ⊢ Δ → ⊢ Γ
--   weaken-⊢Γ base ε = ε
--   weaken-⊢Γ (step x) (c ∙ x₁) = weaken-⊢Γ x c
--   weaken-⊢Γ (pop! x) (c ∙ x₁) = weaken-⊢Γ x c ∙ weaken-Γ⊢A x x₁

--   weaken-Γ⊢A : ∀ {Γ Δ A} → Γ ⊆ Δ → Δ ⊢ A → Γ ⊢ A
--   weaken-Γ⊢A x (ℕ-i x₁) = ℕ-i (weaken-⊢Γ x x₁)
--   weaken-Γ⊢A x (U-i x₁) = U-i (weaken-⊢Γ x x₁)
--   weaken-Γ⊢A x (Π-i t t₁) = Π-i (weaken-Γ⊢A x t) (weaken-Γ⊢A (pop! x) t₁)
--   weaken-Γ⊢A x (univ-refl-term x₁) = univ-refl-term (weaken-Γ⊢t∷A x x₁)

--   weaken-Γ⊢t∷A : ∀ {Γ Δ A t} → Γ ⊆ Δ → Δ ⊢ t ∷ A → Γ ⊢ t ∷ A
--   weaken-Γ⊢t∷A x t = {!!}

wellformed-Γ⊢t∷A : ∀ {Γ a A} → Γ ⊢ a ∷ A → ⊢ Γ
wellformed-Γ⊢t∷A (var-i x x₁) = x
wellformed-Γ⊢t∷A (univ-ℕ-i x) = x
wellformed-Γ⊢t∷A (univ-Π-i x x₁) = wellformed-Γ⊢t∷A x
wellformed-Γ⊢t∷A (λ-i x) with wellformed-Γ⊢t∷A x
wellformed-Γ⊢t∷A (λ-i x₁) | q ∙ x = q
  -- wellformed-Γ⊢t∷A (weaken-Γ⊢t∷A (step (⊆-refl _)) x)
wellformed-Γ⊢t∷A (fun-e x x₁) = wellformed-Γ⊢t∷A x₁
wellformed-Γ⊢t∷A (zero x) = x
wellformed-Γ⊢t∷A (suc x) = wellformed-Γ⊢t∷A x
wellformed-Γ⊢t∷A (natrec-i x x₁ x₂) = wellformed-Γ⊢t∷A x₁
wellformed-Γ⊢t∷A (eq-type-term x x₁) = wellformed-Γ⊢t∷A x

wellformed-Γ⊢A : ∀ {Γ A} → Γ ⊢ A → ⊢ Γ
wellformed-Γ⊢A (ℕ-i x) = x
wellformed-Γ⊢A (U-i x) = x
wellformed-Γ⊢A (Π-i x x₁) = wellformed-Γ⊢A x
wellformed-Γ⊢A (univ-refl-term x) = wellformed-Γ⊢t∷A x

inversion-natrec :  ∀ {Γ c g A C} → Γ ⊢ natrec C c g ∷ A → Γ ⊢ A ≡ Π ℕ ▹ C
inversion-natrec (natrec-i x d d₁) = {!!}
inversion-natrec (eq-type-term d x) = {!!}

inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (fun-e d d₁) = _ , _ , d , d₁ , {!!}
inversion-app (eq-type-term d x) = {!!}

-- inverse typing lemmas
lemma1 : ∀ {Γ c g m A C} → Γ ⊢ natrec C c g ∘ m ∷ A → Γ ⊢ A ≡ C [ m ]
lemma1 (fun-e x x₁) = {!!}
lemma1 (eq-type-term x x₁) = trans (sym x₁) (lemma1 x)

lemmaℕ0 : ∀ {Γ C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
lemmaℕ0 (zero x) = refl (ℕ-i x)
lemmaℕ0 (eq-type-term x x₁) = trans (sym x₁) (lemmaℕ0 x)

lemmaℕ : ∀ {Γ t C} → Γ ⊢ suc t ∷ C → Γ ⊢ C ≡ ℕ
lemmaℕ (suc x) = refl (ℕ-i (wellformed-Γ⊢t∷A x))
lemmaℕ (eq-type-term x x₁) = trans (sym x₁) (lemmaℕ x)

subset : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ-refl x) = univ-refl {!!}
