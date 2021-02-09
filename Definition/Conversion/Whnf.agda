{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Whnf where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Conversion

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

mutual
  -- Extraction of neutrality from algorithmic equality of neutrals.
  ne~↑ : ∀ {t u A}
       → Γ ⊢ t ~ u ↑ A
       → Neutral t × Neutral u
  ne~↑ (var-refl x₁ x≡y) = var _ , var _
  ne~↑ (app-cong x x₁) = let _ , q , w = ne~↓ x
                         in  ∘ₙ q , ∘ₙ w
  ne~↑ (fst-cong x) =
    let _ , pNe , rNe = ne~↓ x
    in  fstₙ pNe , fstₙ rNe
  ne~↑ (snd-cong x) =
    let _ , pNe , rNe = ne~↓ x
    in  sndₙ pNe , sndₙ rNe
  ne~↑ (natrec-cong x x₁ x₂ x₃) = let _ , q , w = ne~↓ x₃
                                  in  natrecₙ q , natrecₙ w
  ne~↑ (Emptyrec-cong x x₁) = let _ , q , w = ne~↓ x₁
                              in Emptyrecₙ q , Emptyrecₙ w

  -- Extraction of neutrality and WHNF from algorithmic equality of neutrals
  -- with type in WHNF.
  ne~↓ : ∀ {t u A}
       → Γ ⊢ t ~ u ↓ A
       → Whnf A × Neutral t × Neutral u
  ne~↓ ([~] A₁ D whnfB k~l) = whnfB , ne~↑ k~l

-- Extraction of WHNF from algorithmic equality of types in WHNF.
whnfConv↓ : ∀ {A B}
          → Γ ⊢ A [conv↓] B
          → Whnf A × Whnf B
whnfConv↓ (U-refl x) = Uₙ , Uₙ
whnfConv↓ (ℕ-refl x) = ℕₙ , ℕₙ
whnfConv↓ (Empty-refl x) = Emptyₙ , Emptyₙ
whnfConv↓ (Unit-refl x) = Unitₙ , Unitₙ
whnfConv↓ (ne x) = let _ , neA , neB = ne~↓ x
                   in  ne neA , ne neB
whnfConv↓ (Π-cong x x₁ x₂) = Πₙ , Πₙ
whnfConv↓ (Σ-cong x x₁ x₂) = Σₙ , Σₙ

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
whnfConv↓Term : ∀ {t u A}
              → Γ ⊢ t [conv↓] u ∷ A
              → Whnf A × Whnf t × Whnf u
whnfConv↓Term (ℕ-ins x) = let _ , neT , neU = ne~↓ x
                           in ℕₙ , ne neT , ne neU
whnfConv↓Term (Empty-ins x) = let _ , neT , neU = ne~↓ x
                              in Emptyₙ , ne neT , ne neU
whnfConv↓Term (Unit-ins x) = let _ , neT , neU = ne~↓ x
                             in Unitₙ , ne neT , ne neU
whnfConv↓Term (ne-ins t u x x₁) =
  let _ , neT , neU = ne~↓ x₁
  in ne x , ne neT , ne neU
whnfConv↓Term (univ x x₁ x₂) = Uₙ , whnfConv↓ x₂
whnfConv↓Term (zero-refl x) = ℕₙ , zeroₙ , zeroₙ
whnfConv↓Term (suc-cong x) = ℕₙ , sucₙ , sucₙ
whnfConv↓Term (η-eq x₁ x₂ y y₁ x₃) = Πₙ , functionWhnf y , functionWhnf y₁
whnfConv↓Term (Σ-η _ _ pProd rProd _ _) = Σₙ , productWhnf pProd , productWhnf rProd
whnfConv↓Term (η-unit _ _ tWhnf uWhnf) = Unitₙ , tWhnf , uWhnf
