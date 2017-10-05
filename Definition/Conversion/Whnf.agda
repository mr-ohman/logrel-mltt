{-# OPTIONS --without-K #-}

module Definition.Conversion.Whnf where

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Conversion

open import Tools.Product


mutual
  -- Extraction of neutrality from algorithmic equality of neutrals.
  ne~↑ : ∀ {t u A Γ}
       → Γ ⊢ t ~ u ↑ A
       → Neutral t × Neutral u
  ne~↑ (var x₁ x≡y) = var _ , var _
  ne~↑ (app x x₁) = let _ , q , w = ne~↓ x
                    in  _∘_ q , _∘_ w
  ne~↑ (natrec x x₁ x₂ x₃) = let _ , q , w = ne~↓ x₃
                             in  natrec q , natrec w

  -- Extraction of neutrality and WHNF from algorithmic equality of neutrals
  -- with type in WHNF.
  ne~↓ : ∀ {t u A Γ}
       → Γ ⊢ t ~ u ↓ A
       → Whnf A × Neutral t × Neutral u
  ne~↓ ([~] A₁ D whnfB k~l) = whnfB , ne~↑ k~l

-- Extraction of WHNF from algorithmic equality of types in WHNF.
whnfConv↓ : ∀ {A B Γ}
          → Γ ⊢ A [conv↓] B
          → Whnf A × Whnf B
whnfConv↓ (U-refl x) = U , U
whnfConv↓ (ℕ-refl x) = ℕ , ℕ
whnfConv↓ (ne x) = let _ , neA , neB = ne~↓ x
                   in  ne neA , ne neB
whnfConv↓ (Π-cong x x₁ x₂) = Π , Π

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
whnfConv↓Term : ∀ {t u A Γ}
              → Γ ⊢ t [conv↓] u ∷ A
              → Whnf A × Whnf t × Whnf u
whnfConv↓Term (ℕ-ins x) = let _ , neT , neU = ne~↓ x
                          in ℕ , ne neT , ne neU
whnfConv↓Term (ne-ins t u x x₁) =
  let _ , neT , neU = ne~↓ x₁
  in ne x , ne neT , ne neU
whnfConv↓Term (univ x x₁ x₂) = U , whnfConv↓ x₂
whnfConv↓Term (zero-refl x) = ℕ , zero , zero
whnfConv↓Term (suc-cong x) = ℕ , suc , suc
whnfConv↓Term (fun-ext x x₁ x₂ y y₁ x₃) = Π , y , y₁
