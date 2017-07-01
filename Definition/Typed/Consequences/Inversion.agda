{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Inversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Nat
open import Tools.Product


inversion-ℕ : ∀ {Γ C} → Γ ⊢ ℕ ∷ C → Γ ⊢ C ≡ U
inversion-ℕ (ℕ x) = refl (U x)
inversion-ℕ (conv x x₁) = trans (sym x₁) (inversion-ℕ x)

inversion-Π : ∀ {F G Γ C}
            → Γ ⊢ Π F ▹ G ∷ C → Γ ⊢ F ∷ U × Γ ∙ F ⊢ G ∷ U × Γ ⊢ C ≡ U
inversion-Π (Π x ▹ x₁) = x , x₁ , refl (U (wfTerm x))
inversion-Π (conv x x₁) = let a , b , c = inversion-Π x
                          in  a , b , trans (sym x₁) c

inversion-zero : ∀ {Γ C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
inversion-zero (zero x) = refl (ℕ x)
inversion-zero (conv x x₁) = trans (sym x₁) (inversion-zero x)

inversion-suc : ∀ {Γ t C} → Γ ⊢ suc t ∷ C → Γ ⊢ t ∷ ℕ × Γ ⊢ C ≡ ℕ
inversion-suc (suc x) = x , refl (ℕ (wfTerm x))
inversion-suc (conv x x₁) =
  let a , b = inversion-suc x
  in  a , trans (sym x₁) b

inversion-natrec : ∀ {Γ c g n A C} → Γ ⊢ natrec C c g n ∷ A
  → (Γ ∙ ℕ ⊢ C)
  × Γ ⊢ c ∷ C [ zero ]
  × Γ ⊢ g ∷ Π ℕ ▹ (C ▹▹ C [ suc (var zero) ]↑)
  × Γ ⊢ n ∷ ℕ
  × Γ ⊢ A ≡ C [ n ]
inversion-natrec (natrec x d d₁ n) = x , d , d₁ , n , refl (substType x n)
inversion-natrec (conv d x) = let a , b , c , d , e = inversion-natrec d
                              in  a , b , c , d , trans (sym x) e

inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (d ∘ d₁) = _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁)
inversion-app (conv d x) = let a , b , c , d , e = inversion-app d
                           in  a , b , c , d , trans (sym x) e

inversion-lam : ∀ {t A Γ} → Γ ⊢ lam t ∷ A →
  ∃₂ λ F G → Γ ⊢ F × (Γ ∙ F ⊢ t ∷ G × Γ ⊢ A ≡ Π F ▹ G)
inversion-lam (lam x x₁) = _ , _ , x , x₁ , refl (Π x ▹ (syntacticTerm x₁))
inversion-lam (conv x x₁) = let a , b , c , d , e = inversion-lam x
                            in  a , b , c , d , trans (sym x₁) e
