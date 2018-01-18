{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.NeTypeEq where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Helper function for the same variable instance of a context have equal types.
varTypeEq′ : ∀ {n R T Γ} → n ∷ R ∈ Γ → n ∷ T ∈ Γ → R PE.≡ T
varTypeEq′ here here = PE.refl
varTypeEq′ (there n∷R) (there n∷T) rewrite varTypeEq′ n∷R n∷T = PE.refl

-- The same variable instance of a context have equal types.
varTypeEq : ∀ {x A B Γ} → Γ ⊢ A → Γ ⊢ B → x ∷ A ∈ Γ → x ∷ B ∈ Γ → Γ ⊢ A ≡ B
varTypeEq A B x∷A x∷B rewrite varTypeEq′ x∷A x∷B = refl A

-- The same neutral term have equal types.
neTypeEq : ∀ {t A B Γ} → Neutral t → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B
neTypeEq (var x) (var x₁ x₂) (var x₃ x₄) =
  varTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
neTypeEq (∘ₙ neT) (t∷A ∘ⱼ t∷A₁) (t∷B ∘ⱼ t∷B₁) with neTypeEq neT t∷A t∷B
... | q = let w = proj₂ (injectivity q)
          in  substTypeEq w (refl t∷A₁)
neTypeEq (natrecₙ neT) (natrecⱼ x t∷A t∷A₁ t∷A₂) (natrecⱼ x₁ t∷B t∷B₁ t∷B₂) =
  refl (substType x₁ t∷B₂)
neTypeEq x (conv t∷A x₁) t∷B = let q = neTypeEq x t∷A t∷B
                               in  trans (sym x₁) q
neTypeEq x t∷A (conv t∷B x₃) = let q = neTypeEq x t∷A t∷B
                               in  trans q x₃
