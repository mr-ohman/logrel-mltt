module Definition.EqualityRelation where

open import Definition.Untyped
open import Definition.Typed hiding (_⊢_≡_; _⊢_≡_∷_)

record EqRelSet : Set₁ where
  constructor eqRel
  field
    _⊢_≅_   : Con Term → (A B : Term)   → Set
    _⊢_≅_∷_ : Con Term → (t u A : Term) → Set

    ≅-Urefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ U ≅ U
    ≅-ℕrefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ

    ≅-sym  : ∀ {A B Γ}   → Γ ⊢ A ≅ B     → Γ ⊢ B ≅ A
    ≅ₜ-sym : ∀ {t u A Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ t ∷ A

    ≅-trans  : ∀ {A B C Γ}   → Γ ⊢ A ≅ B     → Γ ⊢ B ≅ C     → Γ ⊢ A ≅ C
    ≅ₜ-trans : ∀ {t u v A Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ v ∷ A → Γ ⊢ t ≅ v ∷ A

    ≅-red : ∀ {A A' B B' Γ}
          → Γ ⊢ A ⇒* A'
          → Γ ⊢ B ⇒* B'
          → Γ ⊢ A' ≅ B'
          → Γ ⊢ A  ≅ B

    ≅ₜ-red : ∀ {a a' b b' A B Γ}
           → Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a' ∷ B
           → Γ ⊢ b ⇒* b' ∷ B
           → Γ ⊢ a' ≅ b' ∷ B
           → Γ ⊢ a  ≅ b ∷ A
