{-# OPTIONS --without-K #-}

module Tools.Sum where

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

id : ∀ {A} → A ⊎ A → A
id (inj₁ x) = x
id (inj₂ x) = x

sym : ∀ {A B} → A ⊎ B → B ⊎ A
sym (inj₁ x) = inj₂ x
sym (inj₂ x) = inj₁ x
