{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Weakening where

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Consequences.Syntactic
open import Definition.Conversion
open import Definition.Conversion.Soundness

open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product

private
  variable
    m n : Nat
    ρ : Wk m n

mutual
  -- Weakening of algorithmic equality of neutrals.
  wk~↑ : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↑ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↑ U.wk ρ A
  wk~↑ {ρ = ρ} [ρ] ⊢Δ (var-refl x₁ x≡y) = var-refl (wkTerm [ρ] ⊢Δ x₁) (PE.cong (wkVar ρ) x≡y)
  wk~↑ ρ ⊢Δ (app-cong {G = G} t~u x) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym (wk-β G))
             (app-cong (wk~↓ ρ ⊢Δ t~u) (wkConv↑Term ρ ⊢Δ x))
  wk~↑ ρ ⊢Δ (fst-cong p~r) =
    fst-cong (wk~↓ ρ ⊢Δ p~r)
  wk~↑ ρ ⊢Δ (snd-cong {G = G} p~r) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x)
             (PE.sym (wk-β G))
             (snd-cong (wk~↓ ρ ⊢Δ p~r))
  wk~↑ {ρ = ρ} {Δ = Δ} [ρ] ⊢Δ (natrec-cong {k} {l} {h} {g} {a₀} {b₀} {F} {G} x x₁ x₂ t~u) =
    PE.subst (λ x → _ ⊢ U.wk ρ (natrec F a₀ h k) ~ _ ↑ x) (PE.sym (wk-β F))
             (natrec-cong (wkConv↑ (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) x)
                          (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) (wk-β F)
                                    (wkConv↑Term [ρ] ⊢Δ x₁))
                          (PE.subst (λ x → Δ ⊢ U.wk ρ h [conv↑] U.wk ρ g ∷ x)
                                    (wk-β-natrec _ F) (wkConv↑Term [ρ] ⊢Δ x₂))
                          (wk~↓ [ρ] ⊢Δ t~u))
  wk~↑ {ρ} {Δ = Δ} [ρ] ⊢Δ (Emptyrec-cong {k} {l} {F} {G} x t~u) =
    Emptyrec-cong (wkConv↑ [ρ] ⊢Δ x) (wk~↓ [ρ] ⊢Δ t~u)

  -- Weakening of algorithmic equality of neutrals in WHNF.
  wk~↓ : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↓ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↓ U.wk ρ A
  wk~↓ {ρ = ρ} [ρ] ⊢Δ ([~] A₁ D whnfA k~l) =
    [~] (U.wk ρ A₁) (wkRed* [ρ] ⊢Δ D) (wkWhnf ρ whnfA) (wk~↑ [ρ] ⊢Δ k~l)

  -- Weakening of algorithmic equality of types.
  wkConv↑ : ∀ {A B Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
          → Γ ⊢ A [conv↑] B
          → Δ ⊢ U.wk ρ A [conv↑] U.wk ρ B
  wkConv↑ {ρ = ρ} [ρ] ⊢Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] (U.wk ρ A′) (U.wk ρ B′) (wkRed* [ρ] ⊢Δ D) (wkRed* [ρ] ⊢Δ D′)
        (wkWhnf ρ whnfA′) (wkWhnf ρ whnfB′) (wkConv↓ [ρ] ⊢Δ A′<>B′)

  -- Weakening of algorithmic equality of types in WHNF.
  wkConv↓ : ∀ {A B Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
         → Γ ⊢ A [conv↓] B
         → Δ ⊢ U.wk ρ A [conv↓] U.wk ρ B
  wkConv↓ ρ ⊢Δ (U-refl x) = U-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (ℕ-refl x) = ℕ-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (Empty-refl x) = Empty-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (Unit-refl x) = Unit-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (ne x) = ne (wk~↓ ρ ⊢Δ x)
  wkConv↓ ρ ⊢Δ (Π-cong x A<>B A<>B₁) =
    let ⊢ρF = wk ρ ⊢Δ x
    in  Π-cong ⊢ρF (wkConv↑ ρ ⊢Δ A<>B) (wkConv↑ (lift ρ) (⊢Δ ∙ ⊢ρF) A<>B₁)
  wkConv↓ ρ ⊢Δ (Σ-cong x A<>B A<>B₁) =
    let ⊢ρF = wk ρ ⊢Δ x
    in  Σ-cong ⊢ρF (wkConv↑ ρ ⊢Δ A<>B) (wkConv↑ (lift ρ) (⊢Δ ∙ ⊢ρF) A<>B₁)

  -- Weakening of algorithmic equality of terms.
  wkConv↑Term : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
             → Γ ⊢ t [conv↑] u ∷ A
             → Δ ⊢ U.wk ρ t [conv↑] U.wk ρ u ∷ U.wk ρ A
  wkConv↑Term {ρ = ρ} [ρ] ⊢Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ (U.wk ρ B) (U.wk ρ t′) (U.wk ρ u′)
         (wkRed* [ρ] ⊢Δ D) (wkRed*Term [ρ] ⊢Δ d) (wkRed*Term [ρ] ⊢Δ d′)
         (wkWhnf ρ whnfB) (wkWhnf ρ whnft′) (wkWhnf ρ whnfu′)
         (wkConv↓Term [ρ] ⊢Δ t<>u)

  -- Weakening of algorithmic equality of terms in WHNF.
  wkConv↓Term : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
             → Γ ⊢ t [conv↓] u ∷ A
             → Δ ⊢ U.wk ρ t [conv↓] U.wk ρ u ∷ U.wk ρ A
  wkConv↓Term ρ ⊢Δ (ℕ-ins x) =
    ℕ-ins (wk~↓ ρ ⊢Δ x)
  wkConv↓Term ρ ⊢Δ (Empty-ins x) =
    Empty-ins (wk~↓ ρ ⊢Δ x)
  wkConv↓Term ρ ⊢Δ (Unit-ins x) =
    Unit-ins (wk~↓ ρ ⊢Δ x)
  wkConv↓Term {ρ = ρ} [ρ] ⊢Δ (ne-ins t u x x₁) =
    ne-ins (wkTerm [ρ] ⊢Δ t) (wkTerm [ρ] ⊢Δ u) (wkNeutral ρ x) (wk~↓ [ρ] ⊢Δ x₁)
  wkConv↓Term ρ ⊢Δ (univ x x₁ x₂) =
    univ (wkTerm ρ ⊢Δ x) (wkTerm ρ ⊢Δ x₁) (wkConv↓ ρ ⊢Δ x₂)
  wkConv↓Term ρ ⊢Δ (zero-refl x) = zero-refl ⊢Δ
  wkConv↓Term ρ ⊢Δ (suc-cong t<>u) = suc-cong (wkConv↑Term ρ ⊢Δ t<>u)
  wkConv↓Term {ρ = ρ} {Δ = Δ} [ρ] ⊢Δ (η-eq {F = F} {G = G} x₁ x₂ y y₁ t<>u) =
    let ⊢F , _ = syntacticΠ (syntacticTerm x₁)
        ⊢ρF = wk [ρ] ⊢Δ ⊢F
    in  η-eq (wkTerm [ρ] ⊢Δ x₁) (wkTerm [ρ] ⊢Δ x₂)
             (wkFunction ρ y) (wkFunction ρ y₁)
             (PE.subst₃ (λ x y z → Δ ∙ U.wk ρ F ⊢ x [conv↑] y ∷ z)
                        (PE.cong₂ _∘_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl)
                        (PE.cong₂ _∘_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl)
                        PE.refl
                        (wkConv↑Term (lift [ρ]) (⊢Δ ∙ ⊢ρF) t<>u))
  wkConv↓Term {ρ = ρ} [ρ] ⊢Δ (Σ-η {G = G} ⊢p ⊢r pProd rProd fstConv sndConv) =
    Σ-η (wkTerm [ρ] ⊢Δ ⊢p)
        (wkTerm [ρ] ⊢Δ ⊢r)
        (wkProduct ρ pProd)
        (wkProduct ρ rProd)
        (wkConv↑Term [ρ] ⊢Δ fstConv)
        (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x)
                  (wk-β G)
                  (wkConv↑Term [ρ] ⊢Δ sndConv))
  wkConv↓Term {ρ = ρ} [ρ] ⊢Δ (η-unit [t] [u] tWhnf uWhnf) =
    η-unit (wkTerm [ρ] ⊢Δ [t]) (wkTerm [ρ] ⊢Δ [u])
           (wkWhnf ρ tWhnf) (wkWhnf ρ uWhnf)
