module Definition.Conversion.Transitivity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Injectivity
open import Definition.LogicalRelation.Consequences.Substitution
open import Definition.LogicalRelation.Consequences.SingleSubst

open import Tools.Nat
open import Tools.Product


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
  trans~↑ : ∀ {t u v A B Γ Δ}
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑ A
         → Δ ⊢ u ~ v ↑ B
         → Γ ⊢ t ~ v ↑ A
         × Γ ⊢ A ≡ B
  trans~↑ Γ≡Δ (var x₁) (var x₂) = var x₁ , {!!}
  trans~↑ Γ≡Δ (app t~u a<>b) (app u~v b<>c) =
    let t~v , ΠFG≡ΠF'G' = trans~↓ Γ≡Δ t~u u~v
        F≡F₁ , G≡G₁ = injectivity ΠFG≡ΠF'G'
        a<>c = transConv↑Term Γ≡Δ F≡F₁ a<>b b<>c
    in  app t~v a<>c , substTypeEq G≡G₁ (soundnessConv↑Term a<>b)
  trans~↑ Γ≡Δ (natrec A<>B a₀<>b₀ aₛ<>bₛ t~u) (natrec B<>C b₀<>c₀ bₛ<>cₛ u~v) =
    let [ ⊢Γ , _ , _ ] = substx Γ≡Δ
        A≡B = soundnessConv↑ A<>B
        F[0]≡F₁[0] = substTypeEq A≡B (refl (zero ⊢Γ))
        ΠℕFs≡ΠℕF₁s = sucCong A≡B
        A<>C = transConv↑ (Γ≡Δ ∙ (refl (ℕ ⊢Γ))) A<>B B<>C
        a₀<>c₀ = transConv↑Term Γ≡Δ F[0]≡F₁[0] a₀<>b₀ b₀<>c₀
        aₛ<>cₛ = transConv↑Term Γ≡Δ ΠℕFs≡ΠℕF₁s aₛ<>bₛ bₛ<>cₛ
        t~v , _ = trans~↓ Γ≡Δ t~u u~v
    in  natrec A<>C a₀<>c₀ aₛ<>cₛ t~v
    ,   substTypeEq A≡B (soundness~↓ t~u)

  trans~↓ : ∀ {t u v A B Γ Δ}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ t ~ u ↓ A
          → Δ ⊢ u ~ v ↓ B
          → Γ ⊢ t ~ v ↓ A
          × Γ ⊢ A ≡ B
  trans~↓ Γ≡Δ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) =
    let t~v , A≡B = trans~↑ Γ≡Δ k~l k~l₁
    in  [~] A₁ D whnfA t~v
    ,   trans (sym (subset* D))
              (trans A≡B
                     (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)))

  transConv↑ : ∀ {A B C Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↑] B
            → Δ ⊢ B [conv↑] C
            → Γ ⊢ A [conv↑] C
  transConv↑ Γ≡Δ ([↑] A' B' D D' whnfA' whnfB' A'<>B')
             ([↑] A'' B'' D₁ D'' whnfA'' whnfB'' A'<>B'') =
    [↑] A' {!!} {!!} {!!} {!!} {!!} (transConv↓ Γ≡Δ A'<>B' {!A'<>B''!})

  transConv↓ : ∀ {A B C Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↓] B
            → Δ ⊢ B [conv↓] C
            → Γ ⊢ A [conv↓] C
  transConv↓ Γ≡Δ (U-refl x) (U-refl x₁) = U-refl x
  transConv↓ Γ≡Δ (ℕ-refl x) (ℕ-refl x₁) = ℕ-refl x
  transConv↓ Γ≡Δ (ne x) (ne x₁) =
    let A~C , U≡U = trans~↑ Γ≡Δ x x₁
    in  ne A~C
  transConv↓ Γ≡Δ (Π-cong x x₁ x₂) (Π-cong x₃ x₄ x₅) =
    Π-cong x (transConv↑ Γ≡Δ x₁ x₄) (transConv↑ (Γ≡Δ ∙ soundnessConv↑ x₁) x₂ x₅)
  -- Refutable cases
  transConv↓ Γ≡Δ (U-refl x) (ne x₁) = {!!}
  transConv↓ Γ≡Δ (ℕ-refl x) (ne x₁) = {!!}
  transConv↓ Γ≡Δ (Π-cong x x₁ x₂) (ne x₃) = {!!}
  transConv↓ Γ≡Δ (ne x) (U-refl x₁) = {!!}
  transConv↓ Γ≡Δ (ne x) (ℕ-refl x₁) = {!!}
  transConv↓ Γ≡Δ (ne x) (Π-cong x₁ x₂ x₃) = {!!}

  transConv↑Term : ∀ {t u v A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] u ∷ A
                → Δ ⊢ u [conv↑] v ∷ B
                → Γ ⊢ t [conv↑] v ∷ A
  transConv↑Term Γ≡Δ A≡B ([↑]ₜ B₁ t' u' D d d' whnfB whnft' whnfu' t<>u)
                 ([↑]ₜ B₂ t'' u'' D₁ d₁ d'' whnfB₁ whnft'' whnfu'' t<>u₁) = {!!}

  transConv↓Term : ∀ {t u v A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↓] u ∷ A
                → Δ ⊢ u [conv↓] v ∷ B
                → Γ ⊢ t [conv↓] v ∷ A
  -- Case explosion, most cases can be refuted
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (ℕ-ins x₂ x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (ne-ins x₂ x₃ x₄) = {!!}
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (univ x₂ x₃ x₄) = {!!}
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (zero-refl x₂) = {!!}
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (suc-cong x₂) = {!!}
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (fun-ext x₂ x₃ x₄ x₅) = {!!}
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (ℕ-ins x₃ x₄) = {!!}
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (ne-ins x₃ x₄ x₅) = {!!}
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (univ x₃ x₄ x₅) = {!!}
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (zero-refl x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (suc-cong x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (fun-ext x₃ x₄ x₅ x₆) = {!!}
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (ℕ-ins x₃ x₄) = {!!}
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (ne-ins x₃ x₄ x₅) = {!!}
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (univ x₃ x₄ x₅) = {!!}
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (zero-refl x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (suc-cong x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (fun-ext x₃ x₄ x₅ x₆) = {!!}
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (ℕ-ins x₁ x₂) = {!!}
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (ne-ins x₁ x₂ x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (univ x₁ x₂ x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (zero-refl x₁) = {!!}
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (fun-ext x₁ x₂ x₃ x₄) = {!!}
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (ℕ-ins x₁ x₂) = {!!}
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (ne-ins x₁ x₂ x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (univ x₁ x₂ x₃) = {!!}
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (suc-cong x₁) = {!!}
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (fun-ext x₁ x₂ x₃ x₄) = {!!}
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (ℕ-ins x₄ x₅) = {!!}
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆) = {!!}
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (univ x₄ x₅ x₆) = {!!}
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (zero-refl x₄) = {!!}
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (suc-cong x₄) = {!!}
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (fun-ext x₄ x₅ x₆ x₇) = {!!}
