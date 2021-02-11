{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution {{eqrel : EqRelSet}} where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Nat
open import Tools.Product
open import Tools.Unit

private
  variable
    k ℓ m n l : Nat
    Γ : Con Term n

-- The validity judgements:
-- We consider expressions that satisfy these judgments valid

mutual
  -- Validity of contexts
  data ⊩ᵛ_ : Con Term n → Set where
    ε : ⊩ᵛ ε
    _∙_ : ∀ {A l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
        → ⊩ᵛ Γ ∙ A

  -- Validity of types
  _⊩ᵛ⟨_⟩_/_ : {n : Nat} (Γ : Con Term n) (l : TypeLevel) (A : Term n) → ⊩ᵛ Γ → Set
  _⊩ᵛ⟨_⟩_/_ {n} Γ l A [Γ] =
    ∀ {k : Nat} {Δ : Con Term k} {σ : Subst k n} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
    → Σ (Δ ⊩⟨ l ⟩ subst σ A) (λ [Aσ]
      → ∀ {σ′} ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
        ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
      → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ′ A / [Aσ])

  -- Logical relation for substitutions from a valid context
  _⊩ˢ_∷_/_/_ : (Δ : Con Term n) (σ : Subst n m) (Γ : Con Term m) ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             → Set
  Δ ⊩ˢ σ ∷ .ε        / ε  / ⊢Δ                = ⊤
  Δ ⊩ˢ σ ∷ .(Γ ∙ A) / (_∙_ {Γ = Γ} {A} {l} [Γ] [A]) / ⊢Δ =
    Σ (Δ ⊩ˢ tail σ ∷ Γ / [Γ] / ⊢Δ) λ [tailσ] →
      (Δ ⊩⟨ l ⟩ head σ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ [tailσ]))

  -- Logical relation for equality of substitutions from a valid context
  _⊩ˢ_≡_∷_/_/_/_ : (Δ : Con Term n) (σ σ′ : Subst n m) (Γ : Con Term m) ([Γ] : ⊩ᵛ Γ)
                    (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Set
  --Δ ⊩ˢ σ ≡ σ′ ∷ Γ / x / y / z = {!   !}
  Δ ⊩ˢ σ ≡ σ′ ∷ .ε       / ε       / ⊢Δ              / [σ] = ⊤
  Δ ⊩ˢ σ ≡ σ′ ∷ .(Γ ∙ A) / (_∙_ {Γ = Γ} {A} {l} [Γ] [A]) / ⊢Δ / [σ] =
    (Δ ⊩ˢ tail σ ≡ tail σ′ ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×
    (Δ ⊩⟨ l ⟩ head σ ≡ head σ′ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ (proj₁ [σ])))


-- Validity of terms
_⊩ᵛ⟨_⟩_∷_/_/_ : (Γ : Con Term n) (l : TypeLevel) (t A : Term n) ([Γ] : ⊩ᵛ Γ)
                 ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A] =
  ∀ {k} {Δ : Con Term k} {σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σ (Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ′} → Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
    → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ′ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

-- Validity of type equality
_⊩ᵛ⟨_⟩_≡_/_/_ : (Γ : Con Term n) (l : TypeLevel) (A B : Term n) ([Γ] : ⊩ᵛ Γ)
                ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A] =
  ∀ {k} {Δ : Con Term k} {σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ B / proj₁ ([A] ⊢Δ [σ])

-- Validity of term equality
_⊩ᵛ⟨_⟩_≡_∷_/_/_ : (Γ : Con Term n) (l : TypeLevel) (t u A : Term n) ([Γ] : ⊩ᵛ Γ)
                    ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A] =
  ∀ {k} {Δ : Con Term k} {σ} → (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

-- Valid term equality with validity of its type and terms
record [_⊩ᵛ⟨_⟩_≡_∷_/_] (Γ : Con Term n) (l : TypeLevel)
                       (t u A : Term n) ([Γ] : ⊩ᵛ Γ) : Set where
  constructor modelsTermEq
  field
    [A]   : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
    [t]   : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
    [u]   : Γ ⊩ᵛ⟨ l ⟩ u ∷ A / [Γ] / [A]
    [t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]

-- Validity of reduction of terms
_⊩ᵛ_⇒_∷_/_ : (Γ : Con Term n) (t u A : Term n) ([Γ] : ⊩ᵛ Γ) → Set
Γ ⊩ᵛ t ⇒ u ∷ A / [Γ] = ∀ {k} {Δ : Con Term k} {σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                       → Δ ⊢ subst σ t ⇒ subst σ u ∷ subst σ A
