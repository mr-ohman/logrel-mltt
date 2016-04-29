module Tools.Context where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Unit using (⊤; tt)

infixl 30 _∙_

data Con (A : Set) : Set where
  ε   : Con A
  _∙_ : Con A → A → Con A

data _∈_ {A : Set} (a : A) : Con A → Set where
  here  : {Γ : Con A}                     → a ∈ Γ ∙ a
  there : {Γ : Con A} {b : A} (h : a ∈ Γ) → a ∈ Γ ∙ b

-- toNat : {A : Set} {a : A} {As : Con A} → a ∈ As → ℕ
-- toNat here = zero
-- toNat (there x) = suc (toNat x)

toNat : ∀ {A} → Con A → Nat
toNat ε = zero
toNat (Γ ∙ x) = suc (toNat Γ)

fromNat : Nat → Con ⊤
fromNat zero = ε
fromNat (suc n) = fromNat n ∙ tt

module NonDependent where
  data _⊆_ {A : Set} : Con A → Con A → Set where
    base : ε ⊆ ε
    step : ∀ {Γ : Con A} {Δ : Con A} {σ} (inc : Γ ⊆ Δ) →  Γ      ⊆ (Δ ∙ σ)
    lift : ∀ {Γ : Con A} {Δ : Con A} {σ} (inc : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ σ)

  untype : ∀ {A} → Con A → Con ⊤
  untype ε = ε
  untype (Γ ∙ x) = untype Γ ∙ tt

  untype-⊆ : ∀ {A} {Γ Δ : Con A} → Γ ⊆ Δ → untype Γ ⊆ untype Δ
  untype-⊆ base = base
  untype-⊆ (step pr) = step (untype-⊆ pr)
  untype-⊆ (lift pr) = lift (untype-⊆ pr)

  weak : ∀ {A : Set} {σ : A} {Γ Δ : Con A} → Γ ⊆ Δ → σ ∈ Γ → σ ∈ Δ
  weak base ()
  weak (step pr) a = there (weak pr a)
  weak (lift pr) here = here
  weak (lift pr) (there a) = there (weak pr a)

  lemma : {A : Set} (Γ : Con A) → ε ⊆ Γ
  lemma ε = base
  lemma (Γ ∙ x) = step (lemma Γ)

  ⊆-refl : {A : Set} (Γ : Con A) → Γ ⊆ Γ
  ⊆-refl ε = base
  ⊆-refl (Γ ∙ x) = lift (⊆-refl Γ)

map : {A B : Set} → (A → B) → Con A → Con B
map f ε = ε
map f (as ∙ x) = map f as ∙ f x
