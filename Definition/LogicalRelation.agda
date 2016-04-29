{-# OPTIONS --no-positivity-check #-}
-- Temporary, should not be used with a final solution

module Definition.LogicalRelation where

open import Tools.Context
open import Definition.Untyped
open import Definition.Typed


mutual
  data _⊩_ (Γ : Con Term) : Term → Set where
    U  : Γ ⊩ U
    -- Or should it be:
    -- U : ∀ {A} → Γ ⊢ A ⇒* U → Γ ⊩ A
    ℕ  : ∀ {A} → Γ ⊢ A ⇒* ℕ → Γ ⊩ A
    ne : ∀ {A K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩ A
    Π  : ∀ {A F G} → Γ ⊢ A ⇒* Π F ▹ G
       → Γ ⊢ A → Γ ⊩ F
       → (∀ {Δ a b} → Δ ⊆ Γ → Δ ⊩ a ≡ b ∷ F → Δ ⊩ G [ a ] ≡ G [ b ])
       → Γ ⊩ A

  data _⊩_≡_ (Γ : Con Term) : Term → Term → Set where
    U  : Γ ⊩ U ≡ U
    ℕ  : ∀ {A B} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* ℕ → Γ ⊩ A ≡ B
    ne : ∀ {A B K M} → Γ ⊢ A ⇒* K → Γ ⊢ B ⇒* M → Neutral K → Neutral M → Γ ⊩ A ≡ B
    Π  : ∀ {A B F G H E} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ B ⇒* Π H ▹ E
       → Γ ⊢ A ≡ B → Γ ⊩ A → Γ ⊩ B → Γ ⊩ F ≡ H
       → (∀ {Δ a} → Δ ⊆ Γ → Δ ⊩ a ∷ F → Δ ⊩ G [ a ] ≡ E [ a ])
       → Γ ⊩ A ≡ B

  data _⊩_∷_ (Γ : Con Term) : Term → Term → Set where
    U    : ∀ {A} → Γ ⊢ A ∷ U → Γ ⊩ A → Γ ⊩ A ∷ U
    ne   : ∀ {A K a} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊢ a ∷ A → Γ ⊩ a ∷ A
    ℕ-ñ  : ∀ {A a ñ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* ñ ∷ ℕ → Γ ⊩ a ∷ A -- TODO fix ñ
    ℕ-ne : ∀ {A a k} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* k ∷ ℕ → Neutral k → Γ ⊩ a ∷ A
    Π    : ∀ {A F G f} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ f ∷ A
         → (∀ {Δ a b} → Δ ⊆ Γ → Δ ⊩ a ≡ b ∷ F → Δ ⊩ f ∘ a ≡ f ∘ b ∷ G [ a ])
         → Γ ⊩ f ∷ A

  data _⊩_≡_∷_ (Γ : Con Term) : Term → Term → Term → Set where
    U    : ∀ {A B} → Γ ⊢ A ∷ U → Γ ⊢ B ∷ U → Γ ⊩ A → Γ ⊩ B → Γ ⊩ A ≡ B ∷ U
    ne   : ∀ {A K a b} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊢ a ≡ b ∷ A → Γ ⊩ a ≡ b ∷ A
    ℕ-ñ  : ∀ {A a b ñ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* ñ ∷ ℕ → Γ ⊢ b ⇒* ñ ∷ ℕ
         → Γ ⊩ a ≡ b ∷ A -- TODO fix ñ
    ℕ-ne : ∀ {A a b k k'} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* k ∷ ℕ → Γ ⊢ b ⇒* k' ∷ ℕ
         → Neutral k → Neutral k' → Γ ⊢ a ≡ b ∷ ℕ → Γ ⊩ a ≡ b ∷ A
    Π    : ∀ {A F G f g} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊩ f ∷ A → Γ ⊩ g ∷ A → Γ ⊢ f ≡ g ∷ A
         → (∀ {Δ a} → Δ ⊆ Γ → Δ ⊩ a ∷ F → Δ ⊩ f ∘ a ≡ g ∘ a ∷ G [ a ])
         → Γ ⊩ f ≡ g ∷ A
