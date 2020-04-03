-- Σ type (also used as existential) and
-- cartesian product (also used as conjunction).

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Tools.Product where

open import Agda.Primitive
open import Agda.Builtin.Sigma public using (Σ; _,_)
open import Agda.Builtin.Sigma using (fst; snd)

--infixr 4 _,_
infixr 2 _×_

-- Dependent pair type (aka dependent sum, Σ type).

private
  variable
      ℓ₁ ℓ₂ ℓ₃ : Level


{-record Σ (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁-}

proj₁ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → Σ A B → A
proj₁ = fst

proj₂ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → (S : Σ A B) → B (fst S)
proj₂ = snd

--open Σ public

-- Existential quantification.

∃ : {A : Set ℓ₁} → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
∃ = Σ _

∃₂ : {A : Set ℓ₁} {B : A → Set ℓ₂}
     (C : (x : A) → B x → Set ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
∃₂ C = ∃ λ a → ∃ λ b → C a b

-- Cartesian product.

_×_ : (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ A (λ x → B)
