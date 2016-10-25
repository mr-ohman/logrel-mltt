module Definition.LogicalRelation.Consequences.Inversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.LogicalRelation.Consequences.Injectivity
open import Definition.LogicalRelation.Consequences.SingleSubst

open import Tools.Context
open import Data.Product


inversion-zero : ∀ {Γ C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
inversion-zero (zero x) = refl (ℕ x)
inversion-zero (conv x x₁) = trans (sym x₁) (inversion-zero x)

inversion-suc : ∀ {Γ t C} → Γ ⊢ suc t ∷ C → Γ ⊢ C ≡ ℕ
inversion-suc (suc x) = refl (ℕ (wfTerm x))
inversion-suc (conv x x₁) = trans (sym x₁) (inversion-suc x)

inversion-natrec : ∀ {Γ c g n A C} → Γ ⊢ natrec C c g n ∷ A → Γ ⊢ A ≡ C [ n ]
inversion-natrec (natrec x d d₁ n) = refl (substType x n)
inversion-natrec (conv d x) = trans (sym x) (inversion-natrec d)

inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (d ∘ d₁) = _ , _ , d , d₁ , refl (substTypeΠ (term-inj d) d₁)
inversion-app (conv d x) = let a , b , c , d , e = inversion-app d
                           in  a , b , c , d , trans (sym x) e
