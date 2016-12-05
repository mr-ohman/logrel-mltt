module Definition.Conversion.Symmetry where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.LogicalRelation.Consequences.Syntactic

open import Tools.Product

-- open import Definition.Conversion.Properties
postulate
  ~-subset : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑ A → Γ ⊢ k ≡ l ∷ A
  convSubset : ∀ {A B Γ} → Γ ⊢ A [conv] B → Γ ⊢ A ≡ B
  convSubsetTerm : ∀ {a b A Γ} → Γ ⊢ a [conv] b ∷ A → Γ ⊢ a ≡ b ∷ A

mutual
  sym~ : ∀ {t u A Γ} → Γ ⊢ t ~ u ↑ A → Γ ⊢ u ~ t ↑ A
  sym~ (var x₁) = var x₁
  sym~ (app t~u x x₁) = {!!} -- Typing issue: expects G [ t ] while the
                             --   obvious solution is of type G [ v ]
  sym~ (suc t~u x) =
    let _ , _ , ⊢u = syntacticEqTerm (~-subset t~u)
    in  suc (sym~ t~u) ⊢u
  sym~ (natrec t~u x x₁ x₂ x₃) = {!!} -- Typing issue: expects F [ k ] while the
                                      --   obvious solution is of type F [ l ]

  symConv : ∀ {A B Γ} → Γ ⊢ A [conv] B → Γ ⊢ B [conv] A
  symConv (reduction x x₁ A<>B) = reduction x₁ x (symConv A<>B)
  symConv (U-refl x) = U-refl x
  symConv (ℕ-refl x) = ℕ-refl x
  symConv (ne x x₁ x₂ x₃) =
    let _ , _ , ⊢B = syntacticEqTerm (~-subset x)
    in  ne (sym~ x) (univ ⊢B) x₃ x₂
  symConv (Π-cong x A<>B A<>B₁) =
    let F≡H = convSubset A<>B
        _ , ⊢H = syntacticEq F≡H
    in  Π-cong ⊢H (symConv A<>B)
               (stabilityConv (reflConEq (wf x) ∙ F≡H) (symConv A<>B₁))

  symConvTerm : ∀ {t u A Γ} → Γ ⊢ t [conv] u ∷ A → Γ ⊢ u [conv] t ∷ A
  symConvTerm (reduction x x₁ x₂ t<>u) = reduction x x₂ x₁ (symConvTerm t<>u)
  symConvTerm (ℕ-ins x x₁ x₂) =
    let _ , _ , ⊢u = syntacticEqTerm (~-subset x)
    in  ℕ-ins (sym~ x) x₁ ⊢u
  symConvTerm (ne-ins x x₁ x₂ x₃) =
    let _ , _ , ⊢u = syntacticEqTerm (~-subset x)
    in  ne-ins (sym~ x) x₁ ⊢u x₃
  symConvTerm (univ x x₁ x₂) = univ x₁ x (symConv x₂)
  symConvTerm (zero-refl x) = zero-refl x
  symConvTerm (suc-cong t<>u) = suc-cong (symConvTerm t<>u)
  symConvTerm (fun-ext x x₁ x₂ t<>u) = fun-ext x x₂ x₁ (symConvTerm t<>u)
