{-# OPTIONS --without-K --rewriting --prop #-}

module Tools.OTT where

open import Agda.Primitive

import Agda.Builtin.Equality as PE
open import Agda.Builtin.Equality.Rewrite
open import Tools.Product
open import Tools.Empty

private
  -- Use builtin Agda equality as the rewrite relation
  infix 4 _↦_
  _↦_ = PE._≡_

  variable
    ℓ  : Level

-- Declare ≡ as heterogeneous, observational equality
-- cf https://jesper.sikanda.be/posts/hack-your-type-theory.html
infix 6 _≡_

postulate
  _≡_  : {A B : Set ℓ} → A → B → Set ℓ

_≢_ : {A B : Set ℓ} → A → B → Set ℓ
x ≢ y = x ≡ y → ⊥

postulate
  refl : {A : Set ℓ} (x : A) → x ≡ x
  cong : {A : Set ℓ} (x y : A) (P : A → Set ℓ) → x ≡ y → P x ≡ P y
  eqEq : {A B C D : Set ℓ}
         (a : A) (b : B) (c : C) (d : D)
       → A ≡ C → B ≡ D
       → a ≡ c → b ≡ d
       → (a ≡ b) ≡ (c ≡ d)

eqEqA : {A B C D : Set ℓ} → A ≡ C → B ≡ D → (A ≡ B) ≡ (C ≡ D)
eqEqA {ℓ = ℓ} A≡C B≡D =
  eqEq _ _ _ _ (refl (Set ℓ)) (refl (Set ℓ)) A≡C B≡D

HEq = _≡_
syntax HEq {A = A} {B = B} x y = x ∈ A ≡ y ∈ B

postulate
  cong-Σ : {A B : Set ℓ}
           {P : A → Set ℓ} {Q : B → Set ℓ}
         → (Σ A λ x → P x) ≡ (Σ B λ y → Q y)
         ↦ (A ≡ B × ∀ (x : A) (y : B) → x ≡ y → P x ≡ Q y)
  cong-, : {A : Set ℓ} {B : Set ℓ}
           {P : A → Set ℓ} {Q : B → Set ℓ}
           (p : Σ A λ x → P x) (r : Σ B λ y → Q y)
         → p ≡ r
         ↦ (proj₁ p ≡ proj₁ r × proj₂ p ≡ proj₂ r)
{-# REWRITE cong-Σ cong-, #-}

postulate
  cong-Π : {A B : Set ℓ}
           {P : A → Set ℓ} {Q : B → Set ℓ}
         → ((x : A) → P x) ≡ ((y : B) → Q y)
         ↦ (B ≡ A × ∀ (x : A) (y : B) → y ≡ x → P x ≡ Q y)
  cong-λ : {A : Set ℓ} {B : Set ℓ}
           {P : A → Set ℓ} {Q : B → Set ℓ}
           (f : (x : A) → P x) (g : (y : B) → Q y)
         → ((λ x → f x) ≡ (λ y → g y))
         ↦ (∀ (x : A) (y : B) (x≡y : x ≡ y) → f x ≡ g y)
{-# REWRITE cong-Π cong-λ #-}

infix 10 _[_⟩ _||_

postulate
  _[_⟩    : {A B : Set ℓ}
          → A → A ≡ B → B         -- Coercion
  _||_    : {A B : Set ℓ}
            (x : A) (Q : A ≡ B)
          → x ∈ A ≡ x [ Q ⟩ ∈ B   -- Coherence

postulate
  coerce-Σ : {A B : Set ℓ}
             {P : A → Set ℓ} {Q : B → Set ℓ}
             {p : Σ A λ x → P x}
             (ΣAP≡ΣBQ : (Σ A λ x → P x) ≡ (Σ B λ y → Q y))
           → _↦_ {A = Σ B λ y → Q y}
             (p [ ΣAP≡ΣBQ ⟩)
             let A≡B   = proj₁ ΣAP≡ΣBQ
                 r₁ = (proj₁ p) [ A≡B ⟩
                 Px≡Qy = proj₂ ΣAP≡ΣBQ (proj₁ p) r₁ (proj₁ p || A≡B)
                 r₂ = (proj₂ p) [ Px≡Qy ⟩
             in  r₁ , r₂
{-# REWRITE coerce-Σ #-}

postulate
  coerce-Π : {A B : Set ℓ}
             {P : A → Set ℓ} {Q : B → Set ℓ}
             {f : (x : A) → P x}
             (ΠAP≡ΠBQ : ((x : A) → P x) ≡ ((y : B) → Q y))
           → _↦_ {A = (y : B) → Q y}
             (f [ ΠAP≡ΠBQ ⟩)
             λ (y : B) →
               let B≡A   : B ≡ A
                   B≡A   = proj₁ ΠAP≡ΠBQ
                   x     : A
                   x     = y [ B≡A ⟩
                   Px≡Qy : P x ≡ Q y
                   Px≡Qy = proj₂ ΠAP≡ΠBQ x y (y || B≡A)
               in f x [ Px≡Qy ⟩
{-# REWRITE coerce-Π #-}

subst : {A : Set ℓ} {x y : A} (P : A → Set ℓ) → x ≡ y → P x → P y
subst P q t = t [ cong _ _ P q ⟩

sym : {A B : Set ℓ}
      (x : A) (y : B)
    → A ≡ B → x ≡ y → y ≡ x
sym {A = A} x y A≡B x≡y =
  let x≡x = refl x
  in  x≡x [ eqEq x x y x A≡B (refl A) x≡y x≡x  ⟩

trans : {A B C : Set ℓ}
        (x : A) (y : B) (z : C)
      → B ≡ C → x ≡ y → y ≡ z → x ≡ z -- This doesn't require A ≡ B .. is that sound?
trans {A = A} x y z B≡C x≡y y≡z = x≡y [ eqEq x y x z (refl A) B≡C (refl x) y≡z ⟩

-- Function extensionality is provable.
ext : {A : Set ℓ} {P : A → Set ℓ}
      (f g : (x : A) → P x)
      (fx≡gx : ∀ (x : A) → f x ≡ g x)
      → f ≡ g
ext {P = P} f g fx≡gx x y x≡y =
  let gx≡gy = refl g x y x≡y
  in  trans (f x) (g x) (g y) (cong x y P x≡y) (fx≡gx x) gx≡gy
