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
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Injectivity
import Definition.LogicalRelation.Consequences.Inequality as WF
open import Definition.LogicalRelation.Consequences.Substitution
open import Definition.LogicalRelation.Consequences.SingleSubst

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE


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

-- TODO: Copied from InitLemma
lemy : ∀ {n R T Γ} → n ∷ R ∈ Γ → n ∷ T ∈ Γ → R PE.≡ T
lemy here here = PE.refl
lemy (there n∷R) (there n∷T) rewrite lemy n∷R n∷T = PE.refl

lem4 : ∀ {x A B Γ} → Γ ⊢ A → Γ ⊢ B → x ∷ A ∈ Γ → x ∷ B ∈ Γ → Γ ⊢ A ≡ B
lem4 A B x∷A x∷B rewrite lemy x∷A x∷B = refl A

lemma3 : ∀ {t A B Γ} → Neutral t → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B
lemma3 (var x) (var x₁ x₂) (var x₃ x₄) =
  lem4 (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
lemma3 (_∘_ neT) (t∷A ∘ t∷A₁) (t∷B ∘ t∷B₁) with lemma3 neT t∷A t∷B
... | q = let w = proj₂ (injectivity q)
          in  substTypeEq w (refl t∷A₁)
lemma3 (natrec neT) (natrec x t∷A t∷A₁ t∷A₂) (natrec x₁ t∷B t∷B₁ t∷B₂) =
  refl (substType x₁ t∷B₂)
lemma3 x (conv t∷A x₁) t∷B = let q = lemma3 x t∷A t∷B
                             in  trans (sym x₁) q
lemma3 x t∷A (conv t∷B x₃) = let q = lemma3 x t∷A t∷B
                             in  trans q x₃
-- TODO: End of above

mutual
  trans~↑ : ∀ {t u v A B Γ Δ}
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑ A
         → Δ ⊢ u ~ v ↑ B
         → Γ ⊢ t ~ v ↑ A
         × Γ ⊢ A ≡ B
  trans~↑ Γ≡Δ (var x₁) (var x₂) =
    var x₁ , lemma3 (var _) x₁ (stabilityTerm (symConEq Γ≡Δ) x₂)
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
    [↑] A' B'' D (stabilityRed* (symConEq Γ≡Δ) D'') whnfA' whnfB''
        (transConv↓ Γ≡Δ A'<>B'
                    (PE.subst (λ x → _ ⊢ x [conv↓] B'')
                              (whrDet*' (D₁ , whnfA'')
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
    let A~C , U≡U = trans~↑ Γ≡Δ x x₁
    in  ne A~C
  transConv↓ Γ≡Δ (Π-cong x x₁ x₂) (Π-cong x₃ x₄ x₅) =
    Π-cong x (transConv↑ Γ≡Δ x₁ x₄) (transConv↑ (Γ≡Δ ∙ soundnessConv↑ x₁) x₂ x₅)
  -- Refutable cases
  transConv↓ Γ≡Δ (U-refl x) (ne ())
  transConv↓ Γ≡Δ (ℕ-refl x) (ne ())
  transConv↓ Γ≡Δ (Π-cong x x₁ x₂) (ne ())
  transConv↓ Γ≡Δ (ne ()) (U-refl x₁)
  transConv↓ Γ≡Δ (ne ()) (ℕ-refl x₁)
  transConv↓ Γ≡Δ (ne ()) (Π-cong x₁ x₂ x₃)

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
                                       (whrDet* (d₁ , whnft'')
                                                (d₁' , whnfu'))
                                       t<>u₁))

  transConv↓Term : ∀ {t u v A B Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↓] u ∷ A
                → Δ ⊢ u [conv↓] v ∷ B
                → Γ ⊢ t [conv↓] v ∷ A
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (ℕ-ins x₂ x₃) =
    ℕ-ins (proj₁ (trans~↑ Γ≡Δ x x₂)) x₁
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (ne-ins x₃ x₄ x₅) =
    ne-ins (proj₁ (trans~↑ Γ≡Δ x x₃)) x₁ x₂
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (univ x₃ x₄ x₅) =
    univ x (stabilityTerm (symConEq Γ≡Δ) x₄) (transConv↑ Γ≡Δ x₂ x₅)
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (zero-refl x₁) =
    zero-refl x
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (suc-cong x₁) =
    suc-cong (transConv↑Term Γ≡Δ A≡B x x₁)
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (fun-ext x₄ x₅ x₆ x₇) =
    let F₁≡F , G₁≡G = injectivity A≡B
    in  fun-ext x x₁ (conv (stabilityTerm (symConEq Γ≡Δ) x₆) (sym A≡B))
                (transConv↑Term (Γ≡Δ ∙ F₁≡F) G₁≡G x₃ x₇)
  -- Refutable cases
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (ne-ins x₂ x₃ x₄) = ⊥-elim (WF.ℕ≢ne x₄ A≡B)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (univ x₂ x₃ x₄) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ℕ-ins () x₁) (zero-refl x₂)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins () x₁) (suc-cong x₂)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x x₁) (fun-ext x₂ x₃ x₄ x₅) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (ℕ-ins x₃ x₄) = ⊥-elim (WF.ℕ≢ne x₂ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (univ x₃ x₄ x₅) = ⊥-elim (WF.U≢ne x₂ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ne-ins () x₁ x₂) (zero-refl x₃)
  transConv↓Term Γ≡Δ A≡B (ne-ins () x₁ x₂) (suc-cong x₃)
  transConv↓Term Γ≡Δ A≡B (ne-ins x x₁ x₂) (fun-ext x₃ x₄ x₅ x₆) = ⊥-elim (WF.Π≢ne x₂ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (ℕ-ins x₃ x₄) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (ne-ins x₃ x₄ x₅) = ⊥-elim (WF.U≢ne x₅ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (zero-refl x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (suc-cong x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (fun-ext x₃ x₄ x₅ x₆) = ⊥-elim (WF.U≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (ℕ-ins () x₂)
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (ne-ins () x₂ x₃)
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (univ x₁ x₂ x₃) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (fun-ext x₁ x₂ x₃ x₄) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (ℕ-ins () x₂)
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (ne-ins () x₂ x₃)
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (univ x₁ x₂ x₃) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (fun-ext x₁ x₂ x₃ x₄) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (ℕ-ins x₄ x₅) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆) = ⊥-elim (WF.Π≢ne x₆ A≡B)
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (univ x₄ x₅ x₆) = ⊥-elim (WF.U≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (zero-refl x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (fun-ext x x₁ x₂ x₃) (suc-cong x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
