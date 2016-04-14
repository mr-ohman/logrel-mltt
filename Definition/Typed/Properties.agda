module Definition.Typed.Properties where

open import Data.Product

open import Tools.Context
open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Data.Nat renaming (ℕ to Nat)

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

mutual
  wkIndex : ∀ {Γ Δ x A} → Γ ⊆ Δ → ⊢ Δ → x ∷ A ∈ Γ → ∃ λ y → y ∷ A ∈ Δ
  wkIndex base ⊢Δ ()
  wkIndex (step pr) (⊢Δ ∙ x) i = let y = wkIndex pr ⊢Δ i
                                 in suc (proj₁ y) , there {!proj₂ y!}
  wkIndex (lift pr) ⊢Δ here = zero , here
  wkIndex (lift pr) (⊢Δ ∙ x) (there i) = let y = wkIndex pr ⊢Δ i
                                         in suc (proj₁ y) , there (proj₂ y)

  wk : ∀ {Γ Δ A} → Γ ⊆ Δ → ⊢ Δ → Γ ⊢ A → Δ ⊢ A
  wk pr ⊢Δ (ℕ-i x) = ℕ-i ⊢Δ
  wk pr ⊢Δ (U-i x) = U-i ⊢Δ
  wk pr ⊢Δ (Π-i A A₁) = let x = wk pr ⊢Δ A
                        in  Π-i x (wk (lift pr) (⊢Δ ∙ x) A₁)
  wk pr ⊢Δ (univ-refl-term x) = univ-refl-term (wkTerm pr ⊢Δ x)

  -- To weaken typed terms, we need to weaken untyped terms most likely
  wkTerm : ∀ {Γ Δ A t} → Γ ⊆ Δ → ⊢ Δ → Γ ⊢ t ∷ A → Δ ⊢ t ∷ A
  wkTerm pr ⊢Δ (var-i x₁ x₂) = var-i ⊢Δ {!!}  --(wkIndex pr ⊢Δ x₂)
  wkTerm pr ⊢Δ (univ-ℕ-i x) = univ-ℕ-i ⊢Δ
  wkTerm pr ⊢Δ (univ-Π-i t t₁) =
    let x = wkTerm pr ⊢Δ t
    in  univ-Π-i x (wkTerm (lift pr) (⊢Δ ∙ univ-refl-term x) t₁)
  wkTerm pr ⊢Δ (λ-i t₁) = λ-i (wkTerm (lift pr) (⊢Δ ∙ {!!}) t₁)
  wkTerm pr ⊢Δ (fun-e t t₁) = fun-e (wkTerm pr ⊢Δ t) (wkTerm pr ⊢Δ t₁)
  wkTerm pr ⊢Δ (zero x) = zero ⊢Δ
  wkTerm pr ⊢Δ (suc t) = suc (wkTerm pr ⊢Δ t)
  wkTerm pr ⊢Δ (natrec-i x t t₁) = {!!}
  wkTerm pr ⊢Δ (eq-type-term t₁ x) = {!!}

inversion-natrec :  ∀ {Γ c g A C} → Γ ⊢ natrec C c g ∷ A → Γ ⊢ A ≡ Π ℕ ▹ C
inversion-natrec (natrec-i x d d₁) =
  Π-eq (refl (ℕ-i (wellformed-Γ⊢t∷A d))) (refl x)
inversion-natrec (eq-type-term d x) = trans (sym x) (inversion-natrec d)

inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (fun-e d d₁) = _ , _ , d , d₁ , refl {!!}
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

subsetTerm : ∀ {Γ A t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst x x₁ x₂ x₃) =
  fun-eq (refl (eq-type-term (natrec-i x x₁ x₂) {!!})) (subsetTerm x₃)
subsetTerm (natrec-zero x x₁ x₂) = natrec-zero x x₁ x₂
subsetTerm (natrec-suc x x₁ x₂ x₃) = natrec-suc x x₁ x₂ x₃
subsetTerm (app-subst x x₁) = fun-eq (subsetTerm x) (refl x₁)
subsetTerm (β-red x x₁) = β-red x x₁
subsetTerm (eq-type-term x x₁) = eq-type-term (subsetTerm x) x₁

subset : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ-refl x) = univ-refl (subsetTerm x)
