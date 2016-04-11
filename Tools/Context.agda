module Tools.Context where

open import Data.Nat

infixl 30 _∙_

data Con (A : Set) : Set where
  ε : Con A
  _∙_ : Con A → A → Con A

data _∈_ {A : Set} (a : A) : Con A → Set where
  here : {Γ : Con A} → a ∈ Γ ∙ a
  there : {Γ : Con A} {b : A} (pr : a ∈ Γ) → a ∈ Γ ∙ b

data _⊆_ {A : Set} : Con A → Con A → Set where
  base : ε ⊆ ε
  step : ∀ {Γ : Con A} {Δ : Con A} {σ} (inc : Γ ⊆ Δ) → Γ ⊆ (Δ ∙ σ)
  pop! : ∀ {Γ : Con A} {Δ : Con A} {σ} (inc : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ σ)

toNat : {A : Set} {a : A} {As : Con A} → a ∈ As → ℕ
toNat here = zero
toNat (there x) = suc (toNat x)

weak : ∀ {A : Set} {σ : A} {Γ Δ : Con A} → Γ ⊆ Δ → σ ∈ Γ → σ ∈ Δ
weak base ()
weak (step pr) a = there (weak pr a)
weak (pop! pr) here = here
weak (pop! pr) (there a) = weak (step pr) a

lemma : {A : Set} (Γ : Con A) → ε ⊆ Γ 
lemma ε = base
lemma (Γ ∙ x) = step (lemma Γ)

⊆-refl : {A : Set} (Γ : Con A) → Γ ⊆ Γ
⊆-refl ε = base
⊆-refl (Γ ∙ x) = pop! (⊆-refl Γ)

map : {A B : Set} → (A → B) → Con A → Con B
map f ε = ε
map f (as ∙ x) = map f as ∙ f x
