{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Definition.Typed.Consequences.Inversion where

open import Definition.Untyped hiding (_∷_; U≢∪; U≢∥)
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Inequality

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)

private
  variable
    n : Nat
    Γ : Con Term n

-- Inversion of U (it has no type).
inversion-U : ∀ {C} → Γ ⊢ U ∷ C → ⊥
inversion-U (conv x x₁) = inversion-U x

-- Inversion of natural number type.
inversion-ℕ : ∀ {C} → Γ ⊢ ℕ ∷ C → Γ ⊢ C ≡ U
inversion-ℕ (ℕⱼ x) = refl (Uⱼ x)
inversion-ℕ (conv x x₁) = trans (sym x₁) (inversion-ℕ x)

-- Inversion of Empty.
inversion-Empty : ∀ {C} → Γ ⊢ Empty ∷ C → Γ ⊢ C ≡ U
inversion-Empty (Emptyⱼ x) = refl (Uⱼ x)
inversion-Empty (conv x x₁) = trans (sym x₁) (inversion-Empty x)

-- Inversion of Unit.
inversion-Unit : ∀ {C} → Γ ⊢ Unit ∷ C → Γ ⊢ C ≡ U
inversion-Unit (Unitⱼ x) = refl (Uⱼ x)
inversion-Unit (conv x x₁) = trans (sym x₁) (inversion-Unit x)

-- Inversion of Π-types.
inversion-Π : ∀ {F G C}
            → Γ ⊢ Π F ▹ G ∷ C → Γ ⊢ F ∷ U × Γ ∙ F ⊢ G ∷ U × Γ ⊢ C ≡ U
inversion-Π (Πⱼ x ▹ x₁) = x , x₁ , refl (Uⱼ (wfTerm x))
inversion-Π (conv x x₁) = let a , b , c = inversion-Π x
                          in  a , b , trans (sym x₁) c

inversion-Σ : ∀ {F G C}
            → Γ ⊢ Σ F ▹ G ∷ C → Γ ⊢ F ∷ U × Γ ∙ F ⊢ G ∷ U × Γ ⊢ C ≡ U
inversion-Σ (Σⱼ x ▹ x₁) = x , x₁ , refl (Uⱼ (wfTerm x))
inversion-Σ (conv x x₁) = let a , b , c = inversion-Σ x
                          in  a , b , trans (sym x₁) c

-- Inversion of ∪-types.
inversion-∪ : ∀ {A B C}
            → Γ ⊢ A ∪ B ∷ C → Γ ⊢ A ∷ U × Γ ⊢ B ∷ U × Γ ⊢ C ≡ U
inversion-∪ (x ∪ⱼ y) = x , y , refl (Uⱼ (wfTerm x))
inversion-∪ (conv x x₁) = let a , b , c = inversion-∪ x
                          in  a , b , trans (sym x₁) c

-- Inversion of ∥-types.
inversion-∥ : ∀ {A C}
            → Γ ⊢ ∥ A ∥ ∷ C → Γ ⊢ A ∷ U × Γ ⊢ C ≡ U
inversion-∥ (∥ x ∥ⱼ) = x , refl (Uⱼ (wfTerm x))
inversion-∥ (conv x x₁) = let a , c = inversion-∥ x
                          in  a , trans (sym x₁) c

-- Inversion of zero.
inversion-zero : ∀ {C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
inversion-zero (zeroⱼ x) = refl (ℕⱼ x)
inversion-zero (conv x x₁) = trans (sym x₁) (inversion-zero x)

-- Inversion of successor.
inversion-suc : ∀ {t C} → Γ ⊢ suc t ∷ C → Γ ⊢ t ∷ ℕ × Γ ⊢ C ≡ ℕ
inversion-suc (sucⱼ x) = x , refl (ℕⱼ (wfTerm x))
inversion-suc (conv x x₁) =
  let a , b = inversion-suc x
  in  a , trans (sym x₁) b

-- Inversion of injl.
inversion-injl : ∀ {t C} → Γ ⊢ injl t ∷ C → ∃₂ λ A B → Γ ⊢ t ∷ A × Γ ⊢ C ≡ A ∪ B
inversion-injl (injlⱼ {A₁} {B₁} {_} h x) = A₁ , B₁ , x , refl (syntacticTerm x ∪ⱼ h)
inversion-injl (conv h x) with inversion-injl h
... | A , B , ⊢t , C≡ = A , B , ⊢t , trans (sym x) C≡

-- Inversion of injr.
inversion-injr : ∀ {t C} → Γ ⊢ injr t ∷ C → ∃₂ λ A B → Γ ⊢ t ∷ B × Γ ⊢ C ≡ A ∪ B
inversion-injr (injrⱼ {A₁} {B₁} {_} h x) = A₁ , B₁ , x , refl (h ∪ⱼ syntacticTerm x)
inversion-injr (conv h x) with inversion-injr h
... | A , B , ⊢t , C≡ = A , B , ⊢t , trans (sym x) C≡

-- Inversion of ∥ᵢ.
inversion-∥ᵢ : ∀ {t C} → Γ ⊢ ∥ᵢ t ∷ C → ∃ λ A → Γ ⊢ t ∷ A × Γ ⊢ C ≡ ∥ A ∥
inversion-∥ᵢ (∥ᵢⱼ {A₁} {_} h) = A₁ , h , refl ∥ syntacticTerm h ∥ⱼ
inversion-∥ᵢ (conv h x) with inversion-∥ᵢ h
... | A , ⊢t , C≡ =
  A , ⊢t , trans (sym x) C≡

-- Inversion of natural recursion.
inversion-natrec : ∀ {c g n A C} → Γ ⊢ natrec C c g n ∷ A
  → (Γ ∙ ℕ ⊢ C)
  × Γ ⊢ c ∷ C [ zero ]
  × Γ ⊢ g ∷ Π ℕ ▹ (C ▹▹ C [ suc (var x0) ]↑)
  × Γ ⊢ n ∷ ℕ
  × Γ ⊢ A ≡ C [ n ]
inversion-natrec (natrecⱼ x d d₁ n) = x , d , d₁ , n , refl (substType x n)
inversion-natrec (conv d x) = let a , b , c , d , e = inversion-natrec d
                              in  a , b , c , d , trans (sym x) e

-- Inversion of application.
inversion-app :  ∀ {f a A} → Γ ⊢ (f ∘ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (d ∘ⱼ d₁) = _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁)
inversion-app (conv d x) = let a , b , c , d , e = inversion-app d
                           in  a , b , c , d , trans (sym x) e

-- Inversion of lambda.
inversion-lam : ∀ {t A} → Γ ⊢ lam t ∷ A →
  ∃₂ λ F G → Γ ⊢ F × (Γ ∙ F ⊢ t ∷ G × Γ ⊢ A ≡ Π F ▹ G)
inversion-lam (lamⱼ x x₁) = _ , _ , x , x₁ , refl (Πⱼ x ▹ (syntacticTerm x₁))
inversion-lam (conv x x₁) = let a , b , c , d , e = inversion-lam x
                            in  a , b , c , d , trans (sym x₁) e

-- Inversion of products.
inversion-prod : ∀ {t u A} → Γ ⊢ prod t u ∷ A →
  ∃₂ λ F G → Γ ⊢ F × (Γ ∙ F ⊢ G × (Γ ⊢ t ∷ F × Γ ⊢ u ∷ G [ t ] × Γ ⊢ A ≡ Σ F ▹ G))
inversion-prod (prodⱼ ⊢F ⊢G ⊢t ⊢u) =
  -- NOTE fundamental theorem not required since prodⱼ has inversion built-in.
  _ , _ , ⊢F , ⊢G , ⊢t , ⊢u , refl (Σⱼ ⊢F ▹ ⊢G )
inversion-prod (conv x x₁) =
  let F , G , a , b , c , d , e = inversion-prod x
  in F , G , a , b , c , d , trans (sym x₁) e

-- Inversion of star.
inversion-star : ∀ {C} → Γ ⊢ star ∷ C → Γ ⊢ C ≡ Unit
inversion-star (starⱼ x) = refl (Unitⱼ x)
inversion-star (conv x x₁) = trans (sym x₁) (inversion-star x)

-- Inversion of products in WHNF.
whnfProduct : ∀ {p F G} → Γ ⊢ p ∷ Σ F ▹ G → Whnf p → Product p
whnfProduct x prodₙ = prodₙ
whnfProduct x (ne pNe) = ne pNe

whnfProduct x Uₙ = ⊥-elim (inversion-U x)
whnfProduct x Πₙ =
  let _ , _ , Σ≡U = inversion-Π x
  in  ⊥-elim (U≢Σ (sym Σ≡U))
whnfProduct x Σₙ =
  let _ , _ , Σ≡U = inversion-Σ x
  in  ⊥-elim (U≢Σ (sym Σ≡U))
whnfProduct x ∪ₙ =
  let _ , _ , Σ≡U = inversion-∪ x
  in ⊥-elim (U≢Σ (sym Σ≡U))
whnfProduct x ∥ₙ =
  let _ , Σ≡U = inversion-∥ x
  in ⊥-elim (U≢Σ (sym Σ≡U))
whnfProduct x ℕₙ = ⊥-elim (U≢Σ (sym (inversion-ℕ x)))
whnfProduct x Unitₙ = ⊥-elim (U≢Σ (sym (inversion-Unit x)))
whnfProduct x Emptyₙ = ⊥-elim (U≢Σ (sym (inversion-Empty x)))
whnfProduct x lamₙ =
  let _ , _ , _ , _ , Σ≡Π = inversion-lam x
  in  ⊥-elim (Π≢Σ (sym Σ≡Π))
whnfProduct x zeroₙ = ⊥-elim (ℕ≢Σ (sym (inversion-zero x)))
whnfProduct x sucₙ =
  let _ , A≡ℕ = inversion-suc x
  in  ⊥-elim (ℕ≢Σ (sym A≡ℕ))
whnfProduct x starₙ = ⊥-elim (Unit≢Σⱼ (sym (inversion-star x)))
whnfProduct x injlₙ =
  let A , B , ⊢t , C≡ = inversion-injl x
  in ⊥-elim (B≢∪ BΣ C≡)
whnfProduct x injrₙ =
  let A , B , ⊢t , C≡ = inversion-injr x
  in ⊥-elim (B≢∪ BΣ C≡)
whnfProduct x ∥ᵢₙ =
  let A , ⊢t , C≡ = inversion-∥ᵢ x
  in ⊥-elim (B≢∥ BΣ C≡)
