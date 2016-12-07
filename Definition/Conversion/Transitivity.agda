module Definition.Conversion.Transitivity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Injectivity
open import Definition.LogicalRelation.Consequences.Substitution
open import Definition.LogicalRelation.Consequences.SingleSubst

open import Tools.Nat
open import Tools.Product

-- open import Definition.Conversion.Properties
postulate
  ~-subset : ∀ {k l A Γ} → Γ ⊢ k ~ l ↓ A → Γ ⊢ k ≡ l ∷ A
  convSubset : ∀ {A B Γ} → Γ ⊢ A [conv↑] B → Γ ⊢ A ≡ B
  convSubsetTerm : ∀ {a b A Γ} → Γ ⊢ a [conv↑] b ∷ A → Γ ⊢ a ≡ b ∷ A

sucCong : ∀ {F G Γ} → Γ ∙ ℕ ⊢ F ≡ G
        → Γ ⊢ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
            ≡ Π ℕ ▹ (G ▹▹ G [ suc (var zero) ]↑)
sucCong F≡G with wfEq F≡G
sucCong F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , _ = syntacticEq F≡G
  in  Π-cong ⊢ℕ (refl ⊢ℕ)
             (Π-cong ⊢F F≡G
                     (wkEq (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢F)
                           (subst↑TypeEq F≡G
                                         (refl (suc (var (⊢Γ ∙ ⊢ℕ) here))))))

mutual
  trans~ : ∀ {t u v A B Γ Δ}
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑ A
         → Δ ⊢ u ~ v ↑ B
         → Γ ⊢ t ~ v ↑ A
         × Γ ⊢ A ≡ B
  -- trans~ Γ≡Δ (reduction D t~u) x = {!!} , {!!}
  trans~ Γ≡Δ (var x₁) (var x₂) = var x₁ , {!!}
  trans~ Γ≡Δ (app t~u a<>b) (app u~v b<>c) =
    let t~v , ΠFG≡ΠF'G' = trans~↓ Γ≡Δ t~u u~v
        F≡F₁ , G≡G₁ = injectivity ΠFG≡ΠF'G'
        a<>c = transConvTerm↑ Γ≡Δ F≡F₁ a<>b b<>c
    in  app t~v a<>c , substTypeEq G≡G₁ (convSubsetTerm a<>b)
  trans~ Γ≡Δ (natrec A<>B a₀<>b₀ aₛ<>bₛ t~u) (natrec B<>C b₀<>c₀ bₛ<>cₛ u~v) =
    let [ ⊢Γ , _ , _ ] = substx Γ≡Δ
        A≡B = convSubset A<>B
        F[0]≡F₁[0] = substTypeEq A≡B (refl (zero ⊢Γ))
        ΠℕFs≡ΠℕF₁s = sucCong A≡B
        A<>C = transConv↑ (Γ≡Δ ∙ (refl (ℕ ⊢Γ))) A<>B B<>C
        a₀<>c₀ = transConvTerm↑ Γ≡Δ F[0]≡F₁[0] a₀<>b₀ b₀<>c₀
        aₛ<>cₛ = transConvTerm↑ Γ≡Δ ΠℕFs≡ΠℕF₁s aₛ<>bₛ bₛ<>cₛ
        t~v , _ = trans~↓ Γ≡Δ t~u u~v
    in  natrec A<>C a₀<>c₀ aₛ<>cₛ t~v
    ,   substTypeEq A≡B (~-subset t~u)

  trans~↓ : ∀ {t u v A B Γ Δ}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ t ~ u ↓ A
          → Δ ⊢ u ~ v ↓ B
          → Γ ⊢ t ~ v ↓ A
          × Γ ⊢ A ≡ B
  trans~↓ Γ≡Δ t~u u~v = {!!}

  transConv↑ : ∀ {A B C Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↑] B
            → Δ ⊢ B [conv↑] C
            → Γ ⊢ A [conv↑] C
  transConv↑ Γ≡Δ A<>B B<>C = {!!}

  transConv↓ : ∀ {A B C Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↓] B
            → Δ ⊢ B [conv↓] C
            → Γ ⊢ A [conv↓] C
  transConv↓ Γ≡Δ A<>B B<>C = {!!}

  transConvTerm↑ : ∀ {t u v A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] u ∷ A
                → Δ ⊢ u [conv↑] v ∷ B
                → Γ ⊢ t [conv↑] v ∷ A
  transConvTerm↑ t<>u u<>v = {!!}

  transConvTerm↓ : ∀ {t u v A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↓] u ∷ A
                → Δ ⊢ u [conv↓] v ∷ B
                → Γ ⊢ t [conv↓] v ∷ A
  transConvTerm↓ t<>u u<>v = {!!}
