-- Disjoint sum type; also used as logical disjunction.

{-# OPTIONS --without-K --safe #-}

module Tools.Sum where

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Idempotency.

id : ∀ {A} → A ⊎ A → A
id (inj₁ x) = x
id (inj₂ x) = x

-- Symmetry.

sym : ∀ {A B} → A ⊎ B → B ⊎ A
sym (inj₁ x) = inj₂ x
sym (inj₂ x) = inj₁ x

-- Bifunctor instances.

first : ∀{A A' B} → (A → A') → A ⊎ B → A' ⊎ B
first f (inj₁ a) = inj₁ (f a)
first f (inj₂ b) = inj₂ b

second : ∀{A B B'} → (B → B') → A ⊎ B → A ⊎ B'
second f (inj₁ a) = inj₁ a
second f (inj₂ b) = inj₂ (f b)
