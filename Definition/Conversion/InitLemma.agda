{-# OPTIONS --without-K #-}

module Definition.Conversion.InitLemma where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion.Stability
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Inequality as WF

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
