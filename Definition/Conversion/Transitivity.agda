{-# OPTIONS --without-K #-}

module Definition.Conversion.Transitivity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Inequality as WF
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE


mutual
  trans~↑ : ∀ {t u v A B Γ Δ}
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑ A
         → Δ ⊢ u ~ v ↑ B
         → Γ ⊢ t ~ v ↑ A
         × Γ ⊢ A ≡ B
  trans~↑ Γ≡Δ (var x₁ x≡y) (var x₂ x≡y₁) =
    var x₁ (PE.trans x≡y x≡y₁)
    , neTypeEq (var _) x₁
               (PE.subst (λ x → _ ⊢ var x ∷ _) (PE.sym x≡y)
                         (stabilityTerm (symConEq Γ≡Δ) x₂))
  trans~↑ Γ≡Δ (app t~u a<>b) (app u~v b<>c) =
    let t~v , ΠFG≡ΠF'G' = trans~↓ Γ≡Δ t~u u~v
        F≡F₁ , G≡G₁ = injectivity ΠFG≡ΠF'G'
        a<>c = transConv↑Term Γ≡Δ F≡F₁ a<>b b<>c
    in  app t~v a<>c , substTypeEq G≡G₁ (soundnessConv↑Term a<>b)
  trans~↑ Γ≡Δ (natrec A<>B a₀<>b₀ aₛ<>bₛ t~u) (natrec B<>C b₀<>c₀ bₛ<>cₛ u~v) =
    let ⊢Γ , _ , _ = substx Γ≡Δ
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
    [↑] A' B'' D (stabilityRed* (symConEq Γ≡Δ) D'') whnfA' whnfB''
        (transConv↓ Γ≡Δ A'<>B'
                    (PE.subst (λ x → _ ⊢ x [conv↓] B'')
                              (whrDet* (D₁ , whnfA'')
                                        (stabilityRed* Γ≡Δ D' , whnfB'))
                              A'<>B''))

  transConv↓ : ∀ {A B C Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↓] B
            → Δ ⊢ B [conv↓] C
            → Γ ⊢ A [conv↓] C
  transConv↓ Γ≡Δ (U-refl x) (U-refl x₁) = U-refl x
  transConv↓ Γ≡Δ (ℕ-refl x) (ℕ-refl x₁) = ℕ-refl x
  transConv↓ Γ≡Δ (ne x) (ne x₁) =
    let A~C , U≡U = trans~↓ Γ≡Δ x x₁
    in  ne A~C
  transConv↓ Γ≡Δ (Π-cong x x₁ x₂) (Π-cong x₃ x₄ x₅) =
    Π-cong x (transConv↑ Γ≡Δ x₁ x₄) (transConv↑ (Γ≡Δ ∙ soundnessConv↑ x₁) x₂ x₅)
  -- Refutable cases
  transConv↓ Γ≡Δ (U-refl x) (ne ([~] A D whnfB ()))
  transConv↓ Γ≡Δ (ℕ-refl x) (ne ([~] A D whnfB ()))
  transConv↓ Γ≡Δ (Π-cong x x₁ x₂) (ne ([~] A D whnfB ()))
  transConv↓ Γ≡Δ (ne ([~] A₁ D whnfB ())) (U-refl x₁)
  transConv↓ Γ≡Δ (ne ([~] A₁ D whnfB ())) (ℕ-refl x₁)
  transConv↓ Γ≡Δ (ne ([~] A₁ D whnfB ())) (Π-cong x₁ x₂ x₃)

  transConv↑Term : ∀ {t u v A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] u ∷ A
                → Δ ⊢ u [conv↑] v ∷ B
                → Γ ⊢ t [conv↑] v ∷ A
  transConv↑Term Γ≡Δ A≡B ([↑]ₜ B₁ t' u' D d d' whnfB whnft' whnfu' t<>u)
                 ([↑]ₜ B₂ t'' u'' D₁ d₁ d'' whnfB₁ whnft'' whnfu'' t<>u₁) =
    let B₁≡B₂ = trans (sym (subset* D))
                      (trans A≡B
                             (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)))
        d₁'' = conv* (stabilityRed*Term (symConEq Γ≡Δ) d'') (sym B₁≡B₂)
        d₁'  = stabilityRed*Term Γ≡Δ (conv* d' B₁≡B₂)
    in  [↑]ₜ B₁ t' u'' D d d₁'' whnfB whnft' whnfu''
             (transConv↓Term Γ≡Δ B₁≡B₂ t<>u
                             (PE.subst (λ x → _ ⊢ x [conv↓] u'' ∷ B₂)
                                       (whrDet*Term (d₁ , whnft'')
                                                (d₁' , whnfu'))
                                       t<>u₁))

  transConv↓Term : ∀ {t u v A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↓] u ∷ A
                → Δ ⊢ u [conv↓] v ∷ B
                → Γ ⊢ t [conv↓] v ∷ A
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (ℕ-ins x₁) =
    ℕ-ins (proj₁ (trans~↓ Γ≡Δ x x₁))
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (ne-ins t' u' x₂ x₃) =
    ne-ins t (conv (stabilityTerm (symConEq Γ≡Δ) u') (sym A≡B)) x
           (proj₁ (trans~↓ Γ≡Δ x₁ x₃))
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (univ x₃ x₄ x₅) =
    univ x (stabilityTerm (symConEq Γ≡Δ) x₄) (transConv↓ Γ≡Δ x₂ x₅)
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (zero-refl x₁) =
    zero-refl x
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (suc-cong x₁) =
    suc-cong (transConv↑Term Γ≡Δ A≡B x x₁)
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ y y₁ x₃) (fun-ext x₄ x₅ x₆ y₂ y₃ x₇) =
    let F₁≡F , G₁≡G = injectivity A≡B
    in  fun-ext x x₁ (conv (stabilityTerm (symConEq Γ≡Δ) x₆) (sym A≡B))
                y y₃ (transConv↑Term (Γ≡Δ ∙ F₁≡F) G₁≡G x₃ x₇)
  -- Refutable cases
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (ne-ins t u x₂ x₃) = ⊥-elim (WF.ℕ≢ne x₂ A≡B)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (univ x₂ x₃ x₄) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ℕ-ins ([~] A D whnfB ())) (zero-refl x₂)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins ([~] A D whnfB ())) (suc-cong x₂)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (fun-ext x₂ x₃ x₄ y y₁ x₅) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (ℕ-ins x₂) = ⊥-elim (WF.ℕ≢ne x (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (univ x₃ x₄ x₅) = ⊥-elim (WF.U≢ne x (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x ([~] A D whnfB ())) (zero-refl x₃)
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x ([~] A D whnfB ())) (suc-cong x₃)
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (fun-ext x₃ x₄ x₅ y y₁ x₆) = ⊥-elim (WF.Π≢ne x (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (ℕ-ins x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (ne-ins t u x₃ x₄) = ⊥-elim (WF.U≢ne x₃ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (zero-refl x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (suc-cong x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (fun-ext x₃ x₄ x₅ y y₁ x₆) = ⊥-elim (WF.U≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (ℕ-ins ([~] A D whnfB ()))
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (ne-ins t u x₁ ([~] A D whnfB ()))
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (univ x₁ x₂ x₃) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (fun-ext x₁ x₂ x₃ y y₁ x₄) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (ℕ-ins ([~] A D whnfB ()))
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (ne-ins t u x₁ ([~] A D whnfB ()))
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (univ x₁ x₂ x₃) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (fun-ext x₁ x₂ x₃ y y₁ x₄) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ y y₁ x₃) (ℕ-ins x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ y y₁ x₃) (ne-ins t u x₄ x₅) = ⊥-elim (WF.Π≢ne x₄ A≡B)
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ y y₁ x₃) (univ x₄ x₅ x₆) = ⊥-elim (WF.U≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ y y₁ x₃) (zero-refl x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ y y₁ x₃) (suc-cong x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))

transConv : ∀ {A B C Γ}
          → Γ ⊢ A [conv↑] B
          → Γ ⊢ B [conv↑] C
          → Γ ⊢ A [conv↑] C
transConv A<>B B<>C =
  let Γ≡Γ = reflConEq (wfEq (soundnessConv↑ A<>B))
  in  transConv↑ Γ≡Γ A<>B B<>C

transConvTerm : ∀ {t u v A Γ}
              → Γ ⊢ t [conv↑] u ∷ A
              → Γ ⊢ u [conv↑] v ∷ A
              → Γ ⊢ t [conv↑] v ∷ A
transConvTerm t<>u u<>v =
  let t≡u = soundnessConv↑Term t<>u
      Γ≡Γ = reflConEq (wfEqTerm t≡u)
      ⊢A , _ , _ = syntacticEqTerm t≡u
  in  transConv↑Term Γ≡Γ (refl ⊢A) t<>u u<>v
