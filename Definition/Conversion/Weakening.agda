module Definition.Conversion.Weakening where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.LogicalRelation.Consequences.Syntactic

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

mutual
  wk~↑ : ∀ {ρ t u A Γ Δ} ([ρ] : ρ ∷ Γ ⊆ Δ) → ⊢ Δ
      → Γ ⊢ t ~ u ↑ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↑ U.wk ρ A
  wk~↑ ρ ⊢Δ (var x₁) = var (wkTerm ρ ⊢Δ x₁)
  wk~↑ ρ ⊢Δ (app {G = G} t~u x) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym (wk-β G))
             (app (wk~↓ ρ ⊢Δ t~u) (wkConv↑Term ρ ⊢Δ x))
  wk~↑ {ρ} {Δ = Δ} [ρ] ⊢Δ (natrec {k} {l} {h} {g} {a₀} {b₀} {F} {G} x x₁ x₂ t~u) =
    PE.subst (λ x → _ ⊢ U.wk ρ (natrec F a₀ h k) ~ _ ↑ x) (PE.sym (wk-β F))
             (natrec (wkConv↑ (lift [ρ]) (⊢Δ ∙ ℕ ⊢Δ) x)
                     (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) (wk-β F)
                               (wkConv↑Term [ρ] ⊢Δ x₁))
                     (PE.subst (λ x → Δ ⊢ U.wk ρ h [conv↑] U.wk ρ g ∷ x)
                               (wk-β-natrec _ F) (wkConv↑Term [ρ] ⊢Δ x₂))
                     (wk~↓ [ρ] ⊢Δ t~u))

  wk~↓ : ∀ {ρ t u A Γ Δ} ([ρ] : ρ ∷ Γ ⊆ Δ) → ⊢ Δ
      → Γ ⊢ t ~ u ↓ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↓ U.wk ρ A
  wk~↓ {ρ} [ρ] ⊢Δ ([~] A₁ D whnfA k~l) =
    [~] (U.wk ρ A₁) (wkRed* [ρ] ⊢Δ D) (wkWhnf ρ whnfA) (wk~↑ [ρ] ⊢Δ k~l)

  wkConv↑ : ∀ {ρ A B Γ Δ} ([ρ] : ρ ∷ Γ ⊆ Δ) → ⊢ Δ
          → Γ ⊢ A [conv↑] B
          → Δ ⊢ U.wk ρ A [conv↑] U.wk ρ B
  wkConv↑ {ρ} [ρ] ⊢Δ ([↑] A' B' D D' whnfA' whnfB' A'<>B') =
    [↑] (U.wk ρ A') (U.wk ρ B') (wkRed* [ρ] ⊢Δ D) (wkRed* [ρ] ⊢Δ D')
        (wkWhnf ρ whnfA') (wkWhnf ρ whnfB') (wkConv↓ [ρ] ⊢Δ A'<>B')

  wkConv↓ : ∀ {ρ A B Γ Δ} ([ρ] : ρ ∷ Γ ⊆ Δ) → ⊢ Δ
         → Γ ⊢ A [conv↓] B
         → Δ ⊢ U.wk ρ A [conv↓] U.wk ρ B
  wkConv↓ ρ ⊢Δ (U-refl x) = U-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (ℕ-refl x) = ℕ-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (ne x) = ne (wk~↑ ρ ⊢Δ x)
  wkConv↓ ρ ⊢Δ (Π-cong x A<>B A<>B₁) =
    let ⊢ρF = wk ρ ⊢Δ x
    in  Π-cong ⊢ρF (wkConv↑ ρ ⊢Δ A<>B) (wkConv↑ (lift ρ) (⊢Δ ∙ ⊢ρF) A<>B₁)

  wkConv↑Term : ∀ {ρ t u A Γ Δ} ([ρ] : ρ ∷ Γ ⊆ Δ) → ⊢ Δ
             → Γ ⊢ t [conv↑] u ∷ A
             → Δ ⊢ U.wk ρ t [conv↑] U.wk ρ u ∷ U.wk ρ A
  wkConv↑Term {ρ} [ρ] ⊢Δ ([↑]ₜ B t' u' D d d' whnfB whnft' whnfu' t<>u) =
    [↑]ₜ (U.wk ρ B) (U.wk ρ t') (U.wk ρ u')
         (wkRed* [ρ] ⊢Δ D) (wkRed*Term [ρ] ⊢Δ d) (wkRed*Term [ρ] ⊢Δ d')
         (wkWhnf ρ whnfB) (wkWhnf ρ whnft') (wkWhnf ρ whnfu')
         (wkConv↓Term [ρ] ⊢Δ t<>u)

  wkConv↓Term : ∀ {ρ t u A Γ Δ} ([ρ] : ρ ∷ Γ ⊆ Δ) → ⊢ Δ
             → Γ ⊢ t [conv↓] u ∷ A
             → Δ ⊢ U.wk ρ t [conv↓] U.wk ρ u ∷ U.wk ρ A
  wkConv↓Term ρ ⊢Δ (ℕ-ins x x₁) =
    ℕ-ins (wk~↑ ρ ⊢Δ x) (wkRed* ρ ⊢Δ x₁)
  wkConv↓Term {ρ} [ρ] ⊢Δ (ne-ins x x₁ x₃) =
    ne-ins (wk~↑ [ρ] ⊢Δ x) (wkRed* [ρ] ⊢Δ x₁) (wkNeutral ρ x₃)
  wkConv↓Term ρ ⊢Δ (univ x x₁ x₂) =
    univ (wkTerm ρ ⊢Δ x) (wkTerm ρ ⊢Δ x₁) (wkConv↑ ρ ⊢Δ x₂)
  wkConv↓Term ρ ⊢Δ (zero-refl x) = zero-refl ⊢Δ
  wkConv↓Term ρ ⊢Δ (suc-cong t<>u) = suc-cong (wkConv↑Term ρ ⊢Δ t<>u)
  wkConv↓Term {ρ} {Δ = Δ} [ρ] ⊢Δ (fun-ext {F = F} {G = G} x x₁ x₂ t<>u) =
    let ⊢ρF = wk [ρ] ⊢Δ x
    in  fun-ext ⊢ρF (wkTerm [ρ] ⊢Δ x₁) (wkTerm [ρ] ⊢Δ x₂)
                (PE.subst₃ (λ x y z → Δ ∙ U.wk ρ F ⊢ x [conv↑] y ∷ z)
                           (PE.cong₂ _∘_ (PE.sym (wkIndex-lift _)) PE.refl)
                           (PE.cong₂ _∘_ (PE.sym (wkIndex-lift _)) PE.refl)
                           PE.refl
                           (wkConv↑Term (lift [ρ]) (⊢Δ ∙ ⊢ρF) t<>u))
