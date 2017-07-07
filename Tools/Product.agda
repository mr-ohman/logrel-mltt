-- Σ type (also used as existential) and
-- cartesian product (also used as conjunction).

{-# OPTIONS --without-K #-}

module Tools.Product where

infixr 4 _,_
infixr 2 _×_

-- Dependent pair type (aka dependent sum, Σ type).

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- Existential quantification.

∃ : {A : Set} → (A → Set) → Set
∃ = Σ _

∃₂ : {A : Set} {B : A → Set}
     (C : (x : A) → B x → Set) → Set
∃₂ C = ∃ λ a → ∃ λ b → C a b

-- Cartesian product.

_×_ : (A B : Set) → Set
A × B = Σ A (λ x → B)
