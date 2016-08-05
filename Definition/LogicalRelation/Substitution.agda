module Definition.LogicalRelation.Substitution where

open import Definition.Untyped
open import Definition.LogicalRelation
open import Definition.Typed

open import Tools.Context

open import Data.Nat
open import Data.Product
open import Data.Unit

import Relation.Binary.PropositionalEquality as PE


mutual
  data ⊩ₛ_ : Con Term → Set where
    ε : ⊩ₛ ε
    _∙_ : ∀ {Γ A l} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ⟨ l ⟩ A / [Γ]
        → ⊩ₛ Γ ∙ A

  _⊩ₛ⟨_⟩_/_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → ⊩ₛ Γ → Set
  Γ ⊩ₛ⟨ l ⟩ A / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
                   → Σ (Δ ⊩⟨ l ⟩ subst σ A)
                       (λ [Aσ] → ∀ {σ'} → Δ ⊩ₛ σ' ∷ Γ / [Γ] / ⊢Δ → Δ ⊩ₛ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ]
                              → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ' A / [Aσ])

  _⊩ₛ_∷_/_/_ : (Δ : Con Term) (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ) → Set
  Δ ⊩ₛ σ ∷ .ε        / ε  / ⊢Δ                = ⊤
  Δ ⊩ₛ σ ∷ .(Γ ∙ A) / (_∙_ {Γ} {A} {l} [Γ] [A]) / ⊢Δ =
    Σ (Δ ⊩ₛ tail σ ∷ Γ / [Γ] / ⊢Δ) λ [tailσ] →
    (Δ ⊩⟨ l ⟩ head σ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ [tailσ]))

  _⊩ₛ_≡_∷_/_/_/_ : (Δ : Con Term) (σ σ' : Subst) (Γ : Con Term) ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ) → Set
  Δ ⊩ₛ σ ≡ σ' ∷ .ε       / ε       / ⊢Δ              / [σ] = ⊤
  Δ ⊩ₛ σ ≡ σ' ∷ .(Γ ∙ A) / (_∙_ {Γ} {A} {l} [Γ] [A]) / ⊢Δ / [σ] =
    (Δ ⊩ₛ tail σ ≡ tail σ' ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×
    (Δ ⊩⟨ l ⟩ head σ ≡ head σ' ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ (proj₁ [σ])))


_⊩ₛ⟨_⟩t_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) ([Γ] : ⊩ₛ Γ) ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ]) → Set
Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σ (Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ'} → Δ ⊩ₛ σ' ∷ Γ / [Γ] / ⊢Δ → Δ ⊩ₛ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ]
    → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ' t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

_⊩ₛ⟨_⟩_≡_/_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) ([Γ] : ⊩ₛ Γ) ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ]) -> Set
Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
  → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ B / proj₁ ([A] ⊢Δ [σ])

record _⊩ₛ⟨_⟩t_≡_∷_/_ (Γ : Con Term) (l : TypeLevel) (t u A : Term) ([Γ] : ⊩ₛ Γ) : Set where
  constructor modelsTermEq
  field
    [A]   : Γ ⊩ₛ⟨ l ⟩ A / [Γ]
    [t]   : Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A]
    [u]   : Γ ⊩ₛ⟨ l ⟩t u ∷ A / [Γ] / [A]
    [t≡u] : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
            → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])
