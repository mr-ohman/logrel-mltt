module Definition.Conversion.Symmetry where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.LogicalRelation.Consequences.Syntactic

open import Tools.Product


mutual
  sym~↑ : ∀ {t u A Γ} → Γ ⊢ t ~ u ↑ A → Γ ⊢ u ~ t ↑ A
  sym~↑ (var x₁) = var x₁
  sym~↑ (app t~u x) = app (sym~↓ {!t~u!}) (symConv↑Term x) -- Typing issue: expects G [ t ] while the
                             --   obvious solution is of type G [ v ]
  sym~↑ (natrec t~u x x₁ x₂) = {!!} -- Typing issue: expects F [ k ] while the
                                      --   obvious solution is of type F [ l ]

  sym~↓ : ∀ {t u A Γ} → Γ ⊢ t ~ u ↓ A → Γ ⊢ u ~ t ↓ A
  sym~↓ ([~] A₁ D whnfA k~l) = [~] A₁ D whnfA (sym~↑ k~l)

  symConv↑ : ∀ {A B Γ} → Γ ⊢ A [conv↑] B → Γ ⊢ B [conv↑] A
  symConv↑ ([↑] A' B' D D' whnfA' whnfB' A'<>B') =
    [↑] B' A' D' D whnfB' whnfA' (symConv↓ A'<>B')

  symConv↓ : ∀ {A B Γ} → Γ ⊢ A [conv↓] B → Γ ⊢ B [conv↓] A
  symConv↓ (U-refl x) = U-refl x
  symConv↓ (ℕ-refl x) = ℕ-refl x
  symConv↓ (ne x) = ne (sym~↑ x)
  symConv↓ (Π-cong x A<>B A<>B₁) =
    let F≡H = soundnessConv↑ A<>B
        _ , ⊢H = syntacticEq F≡H
    in  Π-cong ⊢H (symConv↑ A<>B)
               (stabilityConv↑ (reflConEq (wf x) ∙ F≡H) (symConv↑ A<>B₁))

  symConv↑Term : ∀ {t u A Γ} → Γ ⊢ t [conv↑] u ∷ A → Γ ⊢ u [conv↑] t ∷ A
  symConv↑Term ([↑]ₜ B t' u' D d d' whnfB whnft' whnfu' t<>u) =
    [↑]ₜ B u' t' D d' d whnfB whnfu' whnft' (symConv↓Term t<>u)

  symConv↓Term : ∀ {t u A Γ} → Γ ⊢ t [conv↓] u ∷ A → Γ ⊢ u [conv↓] t ∷ A
  symConv↓Term (ℕ-ins x x₁) = ℕ-ins (sym~↑ x) x₁
  symConv↓Term (ne-ins x x₁ x₂) = ne-ins (sym~↑ x) x₁ x₂
  symConv↓Term (univ x x₁ x₂) = univ x₁ x (symConv↑ x₂)
  symConv↓Term (zero-refl x) = zero-refl x
  symConv↓Term (suc-cong t<>u) = suc-cong (symConv↑Term t<>u)
  symConv↓Term (fun-ext x x₁ x₂ t<>u) = fun-ext x x₂ x₁ (symConv↑Term t<>u)
