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
  data ⊨⟨_⟩_ (l : TypeLevel) : Con Term → Set where
    ε : ⊨⟨ l ⟩ ε
    _∙_ : ∀ {Γ A} ([Γ] : ⊨⟨ l ⟩ Γ) → Γ ⊨⟨ l ⟩ A / [Γ]
        → ⊨⟨ l ⟩ Γ ∙ A

  _⊨⟨_⟩_/_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → ⊨⟨ l ⟩ Γ → Set
  Γ ⊨⟨ l ⟩ A / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ)
                   → Σ (Δ ⊩⟨ l ⟩ subst σ A)
                       (λ [Aσ] → ∀ {σ'} → Δ ⊨⟨ l ⟩ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ]
                              → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ' A / [Aσ])

  _⊨⟨_⟩_∷_/_/_ : (Δ : Con Term) (l : TypeLevel) (σ : Subst) (Γ : Con Term) ([Γ] : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ) → Set
  Δ ⊨⟨ l ⟩ σ ∷ .ε        / ε  / ⊢Δ                = ⊤
  Δ ⊨⟨ l ⟩ σ ∷ .(Γ ∙ A) / (_∙_ {Γ} {A} [Γ] [A]) / ⊢Δ =
    Σ (Δ ⊨⟨ l ⟩ tail σ ∷ Γ / [Γ] / ⊢Δ) λ [tailσ] →
    (Δ ⊩⟨ l ⟩ head σ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ [tailσ]))

  _⊨⟨_⟩_≡_∷_/_/_/_ : (Δ : Con Term) (l : TypeLevel) (σ σ' : Subst) (Γ : Con Term) ([Γ] : ⊨⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ) ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ) → Set
  Δ ⊨⟨ l ⟩ σ ≡ σ' ∷ .ε       / ε       / ⊢Δ              / [σ] = ⊤
  Δ ⊨⟨ l ⟩ σ ≡ σ' ∷ .(Γ ∙ A) / (_∙_ {Γ} {A} [Γ] [A]) / ⊢Δ / [σ] =
    (Δ ⊨⟨ l ⟩ tail σ ≡ tail σ' ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×
    (Δ ⊩⟨ l ⟩ head σ ≡ head σ' ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ (proj₁ [σ])))


_⊨⟨_⟩t_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) ([Γ] : ⊨⟨ l ⟩ Γ) ([A] : Γ ⊨⟨ l ⟩ A / [Γ]) → Set
Γ ⊨⟨ l ⟩t t ∷ A / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σ (Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ'} → Δ ⊨⟨ l ⟩ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ]
    → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ' t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

_⊨⟨_⟩_≡_/_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) ([Γ] : ⊨⟨ l ⟩ Γ) ([A] : Γ ⊨⟨ l ⟩ A / [Γ]) -> Set
Γ ⊨⟨ l ⟩ A ≡ B / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ)
  → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ B / proj₁ ([A] ⊢Δ [σ])

record _⊨⟨_⟩t_≡_∷_/_ (Γ : Con Term) (l : TypeLevel) (t u A : Term) ([Γ] : ⊨⟨ l ⟩ Γ) : Set where
  constructor modelsTermEq
  field
    [A]   : Γ ⊨⟨ l ⟩ A / [Γ]
    [t]   : Γ ⊨⟨ l ⟩t t ∷ A / [Γ] / [A]
    [u]   : Γ ⊨⟨ l ⟩t u ∷ A / [Γ] / [A]
    [t≡u] : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊨⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ)
            → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])
