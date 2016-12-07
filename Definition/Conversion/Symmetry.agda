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
  ~-subset : ∀ {k l A Γ} → Γ ⊢ k ~ l ↓ A → Γ ⊢ k ≡ l ∷ A
  convSubset : ∀ {A B Γ} → Γ ⊢ A [conv↑] B → Γ ⊢ A ≡ B
  convSubsetTerm : ∀ {a b A Γ} → Γ ⊢ a [conv↑] b ∷ A → Γ ⊢ a ≡ b ∷ A

mutual
  sym~ : ∀ {t u A Γ} → Γ ⊢ t ~ u ↑ A → Γ ⊢ u ~ t ↑ A
  -- sym~ (reduction D k~l) = reduction D (sym~ k~l)
  sym~ (var x₁) = var x₁
  sym~ (app t~u x) = {!!} -- Typing issue: expects G [ t ] while the
                             --   obvious solution is of type G [ v ]
  sym~ (natrec t~u x x₁ x₂) = {!!} -- Typing issue: expects F [ k ] while the
                                      --   obvious solution is of type F [ l ]

  sym~↓ : ∀ {t u A Γ} → Γ ⊢ t ~ u ↑ A → Γ ⊢ u ~ t ↓ A
  sym~↓ = {!!}

  symConv↑ : ∀ {A B Γ} → Γ ⊢ A [conv↑] B → Γ ⊢ B [conv↑] A
  symConv↑ = {!!}

  symConv : ∀ {A B Γ} → Γ ⊢ A [conv↓] B → Γ ⊢ B [conv↓] A
  --symConv (reduction x x₁ A<>B) = reduction x₁ x (symConv A<>B)
  symConv (U-refl x) = U-refl x
  symConv (ℕ-refl x) = ℕ-refl x
  symConv (ne x) = {!!}
    -- let _ , _ , ⊢B = syntacticEqTerm (~-subset x)
    -- in  ne (sym~ x) (univ ⊢B)
  symConv (Π-cong x A<>B A<>B₁) =
    let F≡H = convSubset A<>B
        _ , ⊢H = syntacticEq F≡H
    in  Π-cong ⊢H (symConv↑ A<>B)
               (stabilityConv↑ (reflConEq (wf x) ∙ F≡H) (symConv↑ A<>B₁))

  symConvTerm↑ : ∀ {t u A Γ} → Γ ⊢ t [conv↑] u ∷ A → Γ ⊢ u [conv↑] t ∷ A
  symConvTerm↑ = {!!}

  symConvTerm : ∀ {t u A Γ} → Γ ⊢ t [conv↓] u ∷ A → Γ ⊢ u [conv↓] t ∷ A
  --symConvTerm (reduction x x₁ x₂ t<>u) = reduction x x₂ x₁ (symConvTerm t<>u)
  symConvTerm (ℕ-ins x x₁) = {!!}
    -- let _ , _ , ⊢u = syntacticEqTerm (~-subset x)
    -- in  ℕ-ins (sym~ x) x₁ ⊢u
  symConvTerm (ne-ins x x₁ x₂) = {!!}
    -- let _ , _ , ⊢u = syntacticEqTerm (~-subset x)
    -- in  ne-ins (sym~ x) x₁ ⊢u x₃
  symConvTerm (univ x x₁ x₂) = univ x₁ x (symConv↑ x₂)
  symConvTerm (zero-refl x) = zero-refl x
  symConvTerm (suc-cong t<>u) = suc-cong (symConvTerm↑ t<>u)
  symConvTerm (fun-ext x x₁ x₂ t<>u) = fun-ext x x₂ x₁ (symConvTerm↑ t<>u)
