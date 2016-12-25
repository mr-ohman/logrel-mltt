{-# OPTIONS --without-K #-}

module Tools.Product where


infixr 4 _,_
infixr 2 _×_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

∃ : {A : Set} → (A → Set) → Set
∃ = Σ _

∃₂ : {A : Set} {B : A → Set}
     (C : (x : A) → B x → Set) → Set
∃₂ C = ∃ λ a → ∃ λ b → C a b

_×_ : (A B : Set) → Set
A × B = Σ A (λ x → B)
