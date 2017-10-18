{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution {{eqrel : EqRelSet}} where

open import Definition.Untyped
open import Definition.LogicalRelation
open import Definition.Typed

open import Tools.Nat
open import Tools.Product
open import Tools.Unit

import Tools.PropositionalEquality as PE


-- The validity judgements:
-- We consider expressions that satisfy these judgments valid

mutual
  -- Validity of contexts
  data ⊩ₛ_ : Con Term → Set where
    ε : ⊩ₛ ε
    _∙_ : ∀ {Γ A l} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ⟨ l ⟩ A / [Γ]
        → ⊩ₛ Γ ∙ A

  -- Validity of types
  _⊩ₛ⟨_⟩_/_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → ⊩ₛ Γ → Set
  Γ ⊩ₛ⟨ l ⟩ A / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                   → Σ (Δ ⊩⟨ l ⟩ subst σ A)
                       (λ [Aσ] → ∀ {σ′} ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                               → ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                               → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ′ A / [Aσ])

  -- Validity of substitutions
  _⊩ˢ_∷_/_/_ : (Δ : Con Term) (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
             → Set
  Δ ⊩ˢ σ ∷ .ε        / ε  / ⊢Δ                = ⊤
  Δ ⊩ˢ σ ∷ .(Γ ∙ A) / (_∙_ {Γ} {A} {l} [Γ] [A]) / ⊢Δ =
    Σ (Δ ⊩ˢ tail σ ∷ Γ / [Γ] / ⊢Δ) λ [tailσ] →
    (Δ ⊩⟨ l ⟩ head σ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ [tailσ]))

  -- Validity of substitution equality
  _⊩ˢ_≡_∷_/_/_/_ : (Δ : Con Term) (σ σ′ : Subst) (Γ : Con Term) ([Γ] : ⊩ₛ Γ)
                    (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Set
  Δ ⊩ˢ σ ≡ σ′ ∷ .ε       / ε       / ⊢Δ              / [σ] = ⊤
  Δ ⊩ˢ σ ≡ σ′ ∷ .(Γ ∙ A) / (_∙_ {Γ} {A} {l} [Γ] [A]) / ⊢Δ / [σ] =
    (Δ ⊩ˢ tail σ ≡ tail σ′ ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×
    (Δ ⊩⟨ l ⟩ head σ ≡ head σ′ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ (proj₁ [σ])))


-- Validity of terms
_⊩ₛ⟨_⟩_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) ([Γ] : ⊩ₛ Γ)
                 ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ]) → Set
Γ ⊩ₛ⟨ l ⟩ t ∷ A / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σ (Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ′} → Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
    → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ′ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

-- Validity of type equality
_⊩ₛ⟨_⟩_≡_/_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) ([Γ] : ⊩ₛ Γ)
                ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ]) → Set
Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ B / proj₁ ([A] ⊢Δ [σ])

-- Validity of term equality
_⊩ₛ⟨_⟩_≡_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) ([Γ] : ⊩ₛ Γ)
                    ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ]) → Set
Γ ⊩ₛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A] =
  ∀ {Δ σ} → (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

-- Valid term equality with validity of its type and terms
record [_⊩ₛ⟨_⟩_≡_∷_/_] (Γ : Con Term) (l : TypeLevel)
                       (t u A : Term) ([Γ] : ⊩ₛ Γ) : Set where
  constructor modelsTermEq
  field
    [A]   : Γ ⊩ₛ⟨ l ⟩ A / [Γ]
    [t]   : Γ ⊩ₛ⟨ l ⟩ t ∷ A / [Γ] / [A]
    [u]   : Γ ⊩ₛ⟨ l ⟩ u ∷ A / [Γ] / [A]
    [t≡u] : Γ ⊩ₛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]

-- Validity of reduction of terms
_⊩ₛ_⇒_∷_/_ : (Γ : Con Term) (t u A : Term) ([Γ] : ⊩ₛ Γ) → Set
Γ ⊩ₛ t ⇒ u ∷ A / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                       → Δ ⊢ subst σ t ⇒ subst σ u ∷ subst σ A
