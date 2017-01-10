module Definition.Conversion.InitLemma where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion.Stability
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Injectivity
open import Definition.LogicalRelation.Consequences.SingleSubst
open import Definition.LogicalRelation.Consequences.Inversion
import Definition.LogicalRelation.Consequences.Inequality as WF

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
open import Tools.Nullary
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

-- natrec-subst* : ∀ {Γ F z s n n'} → Γ ∙ ℕ ⊢ F → Γ ⊢ z ∷ F [ zero ]
--               → Γ ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
--               → Γ ⊢ n ⇒* n' ∷ ℕ
--               → Γ ⊢ natrec F z s n ⇒* natrec F z s n' ∷ F [ n ]
-- natrec-subst* F z s (id x) = id (natrec F z s x)
-- natrec-subst* F z s (x ⇨ y) =
--   (natrec-subst F z s x) ⇨
--   (conv* (natrec-subst* F z s y)
--          (sym (substTypeEq (refl F) (subsetTerm x))))

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

-- lemma4 : ∀ {v k R T Γ}
--        → Neutral k → Γ ⊢ v ∷ R → Γ ⊢ v ∷ T → Γ ⊢ v ⇒ k ∷ R
--        → Γ ⊢ T ≡ R
-- lemma4 neK v∷R v∷T (conv d x) =
--   let q = lemma4 neK (conv v∷R (sym x)) v∷T d
--   in  trans q x
-- lemma4 (_∘_ neU) v∷R v∷T (app-subst d x) =
--   let F , G , t , a , A≡G[a] = inversion-app v∷T
--       q = lemma4 neU (redFirstTerm d) t d
--       w , r = injectivity q
--   in  trans A≡G[a] (substTypeEq r (refl a))
-- lemma4 neK v∷R v∷T (β-red x x₁ x₂) =
--   let F , G , t , a , A≡G[a] = inversion-app v∷T
--       F₁ , G₁ , t₁ , eq = inversion-lam t
--       Feq , Geq = injectivity eq
--       q = lemma3 {!{- Neutral (t [ a ]) → Neutral t -}!}
--                  (conv (stabilityTerm ((reflConEq (wf x)) ∙ {!!}) t₁) {!!}) x₁
--   in  trans A≡G[a] (substTypeEq q (refl x₂))
-- lemma4 neK v∷R v∷T (natrec-subst x x₁ x₂ d) =
--   let _ , _ , _ , _ , d = inversion-natrec v∷T
--   in  d
-- lemma4 neK v∷R v∷T (natrec-zero x x₁ x₂) =
--   let _ , _ , _ , _ , d = inversion-natrec v∷T
--   in  d
-- lemma4 neK v∷R v∷T (natrec-suc x x₁ x₂ x₃) =
--   let _ , _ , _ , _ , d = inversion-natrec v∷T
--   in  d
