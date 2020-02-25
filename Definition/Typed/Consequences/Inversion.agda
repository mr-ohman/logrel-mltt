{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Inversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Inequality

open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)


-- Inversion of U (it has no type).
inversion-U : ∀ {Γ C} → Γ ⊢ U ∷ C → ⊥
inversion-U (conv x x₁) = inversion-U x

-- Inversion of natural number type.
inversion-ℕ : ∀ {Γ C} → Γ ⊢ ℕ ∷ C → Γ ⊢ C ≡ U
inversion-ℕ (ℕⱼ x) = refl (Uⱼ x)
inversion-ℕ (conv x x₁) = trans (sym x₁) (inversion-ℕ x)

-- Inversion of Empty.
inversion-Empty : ∀ {Γ C} → Γ ⊢ Empty ∷ C → Γ ⊢ C ≡ U
inversion-Empty (Emptyⱼ x) = refl (Uⱼ x)
inversion-Empty (conv x x₁) = trans (sym x₁) (inversion-Empty x)

-- Inversion of Unit.
inversion-Unit : ∀ {Γ C} → Γ ⊢ Unit ∷ C → Γ ⊢ C ≡ U
inversion-Unit (Unitⱼ x) = refl (Uⱼ x)
inversion-Unit (conv x x₁) = trans (sym x₁) (inversion-Unit x)

-- Inversion of Π-types.
inversion-Π : ∀ {F G Γ C}
            → Γ ⊢ Π F ▹ G ∷ C → Γ ⊢ F ∷ U × Γ ∙ F ⊢ G ∷ U × Γ ⊢ C ≡ U
inversion-Π (Πⱼ x ▹ x₁) = x , x₁ , refl (Uⱼ (wfTerm x))
inversion-Π (conv x x₁) = let a , b , c = inversion-Π x
                          in  a , b , trans (sym x₁) c

-- Inversion of zero.
inversion-zero : ∀ {Γ C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
inversion-zero (zeroⱼ x) = refl (ℕⱼ x)
inversion-zero (conv x x₁) = trans (sym x₁) (inversion-zero x)

-- Inversion of successor.
inversion-suc : ∀ {Γ t C} → Γ ⊢ suc t ∷ C → Γ ⊢ t ∷ ℕ × Γ ⊢ C ≡ ℕ
inversion-suc (sucⱼ x) = x , refl (ℕⱼ (wfTerm x))
inversion-suc (conv x x₁) =
  let a , b = inversion-suc x
  in  a , trans (sym x₁) b

-- Inversion of natural recursion.
inversion-natrec : ∀ {Γ c g n A C} → Γ ⊢ natrec C c g n ∷ A
  → (Γ ∙ ℕ ⊢ C)
  × Γ ⊢ c ∷ C [ zero ]
  × Γ ⊢ g ∷ Π ℕ ▹ (C ▹▹ C [ suc (var 0) ]↑)
  × Γ ⊢ n ∷ ℕ
  × Γ ⊢ A ≡ C [ n ]
inversion-natrec (natrecⱼ x d d₁ n) = x , d , d₁ , n , refl (substType x n)
inversion-natrec (conv d x) = let a , b , c , d , e = inversion-natrec d
                              in  a , b , c , d , trans (sym x) e

-- Inversion of application.
inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (d ∘ⱼ d₁) = _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁)
inversion-app (conv d x) = let a , b , c , d , e = inversion-app d
                           in  a , b , c , d , trans (sym x) e

-- Inversion of lambda.
inversion-lam : ∀ {t A Γ} → Γ ⊢ lam t ∷ A →
  ∃₂ λ F G → Γ ⊢ F × (Γ ∙ F ⊢ t ∷ G × Γ ⊢ A ≡ Π F ▹ G)
inversion-lam (lamⱼ x x₁) = _ , _ , x , x₁ , refl (Πⱼ x ▹ (syntacticTerm x₁))
inversion-lam (conv x x₁) = let a , b , c , d , e = inversion-lam x
                            in  a , b , c , d , trans (sym x₁) e

-- Inversion of star.
inversion-star : ∀ {Γ C} → Γ ⊢ star ∷ C → Γ ⊢ C ≡ Unit
inversion-star (starⱼ x) = refl (Unitⱼ x)
inversion-star (conv x x₁) = trans (sym x₁) (inversion-star x)

-- Inversion of WHNF elements of Unit.
whnfUnitary : ∀ {Γ e} → Γ ⊢ e ∷ Unit → Whnf e → Unitary e
whnfUnitary (conv [e] x) starₙ = starₙ
whnfUnitary (starⱼ x) starₙ = starₙ
whnfUnitary [e] (ne eNe) = ne eNe

-- Refutable cases
whnfUnitary (conv [e] A≡Unit) Uₙ = ⊥-elim (inversion-U [e])
whnfUnitary {Γ} (conv [e] A≡Unit) Πₙ =
  let _ , _ , A≡U = inversion-Π [e]
  in  ⊥-elim (U≢Unitⱼ (trans (sym A≡U) A≡Unit))
whnfUnitary (conv [e] A≡Unit) ℕₙ =
  ⊥-elim (U≢Unitⱼ (trans (sym (inversion-ℕ [e])) A≡Unit))
whnfUnitary (conv [e] A≡Unit) Emptyₙ =
  ⊥-elim (U≢Unitⱼ (trans (sym (inversion-Empty [e])) A≡Unit))
whnfUnitary (conv [e] A≡Unit) Unitₙ =
  ⊥-elim (U≢Unitⱼ (trans (sym (inversion-Unit [e])) A≡Unit))
whnfUnitary (conv [e] A≡Unit) lamₙ =
  let _ , _ , _ , _ , A≡Π = inversion-lam [e]
  in  ⊥-elim (Unit≢Πⱼ (trans (sym A≡Unit) A≡Π))
whnfUnitary (conv [e] A≡Unit) zeroₙ =
  ⊥-elim (ℕ≢Unitⱼ (trans (sym (inversion-zero [e])) A≡Unit))
whnfUnitary (conv [e] A≡Unit) sucₙ =
  let _ , A≡ℕ = inversion-suc [e]
  in  ⊥-elim (ℕ≢Unitⱼ (trans (sym A≡ℕ) A≡Unit))
