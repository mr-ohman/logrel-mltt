{-# OPTIONS --without-K #-}

module Definition.Conversion.Conversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  convConv↑Term : ∀ {t u A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] u ∷ A
                → Δ ⊢ t [conv↑] u ∷ B
  convConv↑Term Γ≡Δ A≡B ([↑]ₜ B₁ t' u' D d d' whnfB whnft' whnfu' t<>u) =
    let _ , ⊢B = syntacticEq A≡B
        B' , whnfB' , D' = fullyReducible ⊢B
        B₁≡B' = trans (sym (subset* D)) (trans A≡B (subset* (red D')))
    in  [↑]ₜ B' t' u' (stabilityRed* Γ≡Δ (red D'))
             (stabilityRed*Term Γ≡Δ (conv* d B₁≡B'))
             (stabilityRed*Term Γ≡Δ (conv* d' B₁≡B')) whnfB' whnft' whnfu'
             (convConv↓Term Γ≡Δ B₁≡B' whnfB' t<>u)

  convConv↓Term : ∀ {t u A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Whnf B
                → Γ ⊢ t [conv↓] u ∷ A
                → Δ ⊢ t [conv↓] u ∷ B
  convConv↓Term Γ≡Δ A≡B whnfB (ℕ-ins x) rewrite ℕ≡A A≡B whnfB =
    ℕ-ins (stability~↓ Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) with ne≡A x A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) | B , neB , PE.refl =
    ne-ins (stabilityTerm Γ≡Δ (conv t A≡B)) (stabilityTerm Γ≡Δ (conv u A≡B))
           neB (stability~↓ Γ≡Δ x₁)
  convConv↓Term Γ≡Δ A≡B whnfB (univ x x₁ x₂) rewrite U≡A A≡B =
    univ (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  convConv↓Term Γ≡Δ A≡B whnfB (zero-refl x) rewrite ℕ≡A A≡B whnfB =
    let _ , ⊢Δ , _ = substx Γ≡Δ
    in  zero-refl ⊢Δ
  convConv↓Term Γ≡Δ A≡B whnfB (suc-cong x) rewrite ℕ≡A A≡B whnfB =
    suc-cong (stabilityConv↑Term Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (fun-ext x x₁ x₂ y y₁ x₃) with Π≡A A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (fun-ext x x₁ x₂ y y₁ x₃) | F' , G' , PE.refl =
    let F≡F' , G≡G' = injectivity A≡B
        ⊢F , ⊢F' = syntacticEq F≡F'
    in  fun-ext (stability Γ≡Δ ⊢F') (stabilityTerm Γ≡Δ (conv x₁ A≡B))
                (stabilityTerm Γ≡Δ (conv x₂ A≡B)) y y₁
                (convConv↑Term (Γ≡Δ ∙ F≡F') G≡G' x₃)

convConvTerm : ∀ {t u A B Γ}
              → Γ ⊢ t [conv↑] u ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t [conv↑] u ∷ B
convConvTerm t<>u A≡B = convConv↑Term (reflConEq (wfEq A≡B)) A≡B t<>u
