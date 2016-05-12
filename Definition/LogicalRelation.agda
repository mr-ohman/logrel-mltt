module Definition.LogicalRelation where

open import Tools.Context

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed

open import Data.Product
open import Data.Sum
import Relation.Binary.PropositionalEquality as PE

infix 20 _⊩⁰_
infix 22 _⊩⁰_≡_/_ _⊩⁰_∷_/_ _⊩⁰_≡_∷_/_

mutual
  -- split into small and big types ⊩⁰, ⊩¹
  -- toSubst : Wk -> Subst
  -- maybe define something like [_,_] : Subst -> Term -> Term; [ s , t ] = subst (consSubst s t)

  data _⊩⁰_ (Γ : Con Term) : Term → Set where
    ℕ  : ∀ {A} → Γ ⊢ A ⇒* ℕ → Γ ⊩⁰ A
    ne : ∀ {A K} → Γ ⊢ A ⇒* K → Neutral K
         → Γ ⊢ K
         → Γ ⊩⁰ A
    Π  : ∀ {F G A} → Γ ⊢ A ⇒* Π F ▹ G
       → Γ ⊢ F
       → Γ ∙ F ⊢ G
       → ([F] : (∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⁰ wkₜ ρ F))
       → ([G] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ → Δ ⊩⁰ wkLiftₜ ρ G [ a ])
       → (∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ) →
                      Δ ⊩⁰ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ → Δ ⊩⁰ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G [ b ] / [G] ρ ⊢Δ [a])
       → Γ ⊩⁰ A



  _⊩⁰_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ A ≡ B / ℕ  A⇒*ℕ = Γ ⊢ B ⇒* ℕ
  Γ ⊩⁰ A ≡ B / ne {K = K} A⇒*K neK ⊢K = ∃ λ M → Γ ⊢ B ⇒* M × Neutral M × Γ ⊢ M × (Γ ⊢ K ≡ M)
  Γ ⊩⁰ A ≡ B / Π  {F} {G} D ⊢F ⊢G [F] [G] G-ext =
    ∃₂ λ F' G'
    → Γ ⊢ A ≡ B
    × Γ ⊩⁰ A
    × Γ ⊩⁰ B
    × (∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⁰ wkₜ ρ F ≡ wkₜ ρ F' / [F] ρ ⊢Δ)
    × (∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
               → Δ ⊩⁰ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G' [ a ] / [G] ρ ⊢Δ [a])

  _⊩⁰_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ t ∷ A / ℕ x = ∃ λ n → Γ ⊢ t ⇒* n ∷ ℕ × Natural n
  Γ ⊩⁰ t ∷ A / ne x x₁ x₂ = Γ ⊢ t ∷ A
  Γ ⊩⁰ f ∷ A / Π {F} {G} x x₁ x₂ [F] [G] x₃ = Γ ⊢ f ∷ A
    × (∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩⁰ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ
                 → Δ ⊩⁰ wkₜ ρ f ∘ a ≡ wkₜ ρ f ∘ b ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])

  _⊩⁰_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ t ≡ u ∷ A / ℕ x = ∃₂ λ k k' → [Natural] (λ n n' → Γ ⊢ n ≡ n' ∷ ℕ) k k' × Γ ⊢ t ⇒* k ∷ ℕ × Γ ⊢ u ⇒* k' ∷ ℕ × Γ ⊢ t ≡ u ∷ ℕ
  Γ ⊩⁰ t ≡ u ∷ A / ne x x₁ x₂ = Γ ⊢ t ≡ u ∷ A
  Γ ⊩⁰ t ≡ u ∷ A / Π {F} {G} x x₁ x₂ [F] [G] x₃ =
    let [A] = Π x x₁ x₂ [F] [G] x₃
    in  Γ ⊩⁰ t ∷ A / [A]
    ×   Γ ⊩⁰ u ∷ A / [A]
    ×   Γ ⊢ t ≡ u ∷ A
    ×   (∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩⁰ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])

mutual
  data _⊩¹_ (Γ : Con Term) : Term → Set where
    U  : Γ ⊩¹ U
    ℕ  : Γ ⊩¹ ℕ
    Π  : ∀ {F G}
       → Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊩¹ F
       → ([F] : (∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩¹ wkₜ ρ F))
       → ([G] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ → Δ ⊩¹ wkLiftₜ ρ G [ a ])
       → (∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                    → Δ ⊩¹ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ → Δ ⊩¹ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G [ b ] / [G] ρ ⊢Δ [a])
       → Γ ⊩¹ Π F ▹ G
    emb : ∀ {A} → Γ ⊩⁰ A → Γ ⊩¹ A

  _⊩¹_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩¹ A → Set
  Γ ⊩¹ .U ≡ t / U = t PE.≡ U
  Γ ⊩¹ .ℕ ≡ t / ℕ = t PE.≡ ℕ
  Γ ⊩¹ .(Π F ▹ G) ≡ t / Π {F} {G} ⊢F ⊢G D [F] [G] G-ext = ∃₂ λ F' G'
    → Term.Π F ▹ G PE.≡ Π F' ▹ G'
    × t PE.≡ Π F' ▹ G'
    × (∀ {Δ} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩¹ wkₜ ρ F ≡ wkₜ ρ F' / [F] ρ ⊢Δ)
    × ((∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                → Δ ⊩¹ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G' [ a ] / [G] ρ ⊢Δ [a]))
  Γ ⊩¹ A ≡ B / emb x = Γ ⊩⁰ A ≡ B / x

  _⊩¹_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩¹ A → Set
  Γ ⊩¹ A ∷ .U / U = Γ ⊢ A ∷ U × Γ ⊩⁰ A
  Γ ⊩¹ a ∷ .ℕ / ℕ = ∃ λ n → Γ ⊢ a ⇒* n ∷ ℕ × Natural n
  Γ ⊩¹ f ∷ .(Π F ▹ G) / Π {F} {G} ⊢F ⊢G D [F] [G] G-ext = Γ ⊢ f ∷ Π F ▹ G
    × (∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩¹ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ
                 → Δ ⊩¹ wkₜ ρ f ∘ a ≡ wkₜ ρ f ∘ b ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
  Γ ⊩¹ t ∷ A / emb x = Γ ⊩⁰ t ∷ A / x

  _⊩¹_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩¹ A → Set
  Γ ⊩¹ t ≡ u ∷ .U / U = Γ ⊢ t ∷ U × Γ ⊢ u ∷ U × Γ ⊢ t ≡ u ∷ U × Γ ⊩⁰ u × Σ (Γ ⊩⁰ t) (λ t₀ → Γ ⊩⁰ t ≡ u / t₀)
  Γ ⊩¹ t ≡ u ∷ .ℕ / ℕ = ∃₂ λ k k' → [Natural] (λ n n' → Γ ⊢ n ≡ n' ∷ ℕ) k k' × Γ ⊢ t ⇒* k ∷ ℕ × Γ ⊢ u ⇒* k' ∷ ℕ × Γ ⊢ t ≡ u ∷ ℕ
  Γ ⊩¹ t ≡ u ∷ .(Π F ▹ G) / Π {F} {G} x x₁ x₂ [F] [G] x₃ =
    let [A] = Π x x₁ x₂ [F] [G] x₃
    in  Γ ⊩¹ t ∷ Π F ▹ G / [A]
    ×   Γ ⊩¹ u ∷ Π F ▹ G / [A]
    ×   Γ ⊢ t ≡ u ∷ Π F ▹ G
    ×   (∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩¹ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
  Γ ⊩¹ t ≡ u ∷ A / emb x = Γ ⊩⁰ t ≡ u ∷ A / x

data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

_⊩⟨_⟩_ : (Γ : Con Term) (T : TypeLevel) → Term → Set
Γ ⊩⟨ ⁰ ⟩ A = Γ ⊩⁰ A
Γ ⊩⟨ ¹ ⟩ A = Γ ⊩¹ A

_⊩⟨_⟩_≡_/_ : (Γ : Con Term) (T : TypeLevel) (A B : Term) → Γ ⊩⟨ T ⟩ A → Set
Γ ⊩⟨ ⁰ ⟩ A ≡ B / [A] = Γ ⊩⁰ A ≡ B / [A]
Γ ⊩⟨ ¹ ⟩ A ≡ B / [A] = Γ ⊩¹ A ≡ B / [A]

_⊩⟨_⟩_∷_/_ : (Γ : Con Term) (T : TypeLevel) (t A : Term) → Γ ⊩⟨ T ⟩ A → Set
Γ ⊩⟨ ⁰ ⟩ t ∷ A / [A] = Γ ⊩⁰ t ∷ A / [A]
Γ ⊩⟨ ¹ ⟩ t ∷ A / [A] = Γ ⊩¹ t ∷ A / [A]

_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term) (T : TypeLevel) (t u A : Term) → Γ ⊩⟨ T ⟩ A → Set
Γ ⊩⟨ ⁰ ⟩ t ≡ u ∷ A / [A] = Γ ⊩⁰ t ≡ u ∷ A / [A]
Γ ⊩⟨ ¹ ⟩ t ≡ u ∷ A / [A] = Γ ⊩¹ t ≡ u ∷ A / [A]

  -- data _⊩_≡_ (Γ : Con Term) : (B : Term) → Term → Set where
  --   U  : Γ ⊩ U ≡ U
  --   ℕ  : ∀ {A B} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* ℕ → Γ ⊩ A ≡ B
  --   ne : ∀ {A B K M} → Γ ⊢ A ⇒* K → Γ ⊢ B ⇒* M → Neutral K → Neutral M →
  --        Γ ⊢ A ≡ B →
  --        Γ ⊩ A ≡ B
  --   Π  : ∀ {A B F G H E} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ B ⇒* Π H ▹ E
  --      → Γ ⊢ A ≡ B → Γ ⊩ A → Γ ⊩ B → Γ ⊩ F ≡ H
  --      → (∀ {Δ a} → Γ ⊆ Δ → Δ ⊩ a ∷ F → Δ ⊩ G [ a ] ≡ E [ a ])
  --      → Γ ⊩ A ≡ B

  -- data _⊩_∷_ (Γ : Con Term) : Term → Term → Set where
  --   U    : ∀ {A} → Γ ⊢ A ∷ U → Γ ⊩ A → Γ ⊩ A ∷ U
  --   ne   : ∀ {A K a} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊢ a ∷ A → Γ ⊩ a ∷ A
  --   ℕ-ñ  : ∀ {A a ñ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* ñ ∷ ℕ → Γ ⊩ a ∷ A -- TODO fix ñ
  --   ℕ-ne : ∀ {A a k} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* k ∷ ℕ → Neutral k → Γ ⊩ a ∷ A
  --   Π    : ∀ {A F G f} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ f ∷ A
  --        → (∀ {Δ a b} → Γ ⊆ Δ → Δ ⊩ a ≡ b ∷ F → Δ ⊩ f ∘ a ≡ f ∘ b ∷ G [ a ])
  --        → Γ ⊩ f ∷ A
  -- data _⊩_≡_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  --   U    : ∀ {A B} → Γ ⊢ A ∷ U → Γ ⊢ B ∷ U → Γ ⊩ A → Γ ⊩ B → Γ ⊩ A ≡ B ∷ U
  --   ne   : ∀ {A K a b} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊢ a ≡ b ∷ A →
  --          -- Neutral a -> Neutral b -> -- ?
  --          Γ ⊩ a ≡ b ∷ A
  --   ℕ-ñ  : ∀ {A a b ñ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* ñ ∷ ℕ → Γ ⊢ b ⇒* ñ ∷ ℕ
  --        → Γ ⊩ a ≡ b ∷ A -- TODO fix ñ
  --   ℕ-ne : ∀ {A a b k k'} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* k ∷ ℕ → Γ ⊢ b ⇒* k' ∷ ℕ
  --        → Neutral k → Neutral k' → Γ ⊢ a ≡ b ∷ ℕ → Γ ⊩ a ≡ b ∷ A
  --   Π    : ∀ {A F G f g} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊩ f ∷ A → Γ ⊩ g ∷ A → Γ ⊢ f ≡ g ∷ A
  --        → (∀ {Δ a} → Γ ⊆ Δ → Δ ⊩ a ∷ F → Δ ⊩ f ∘ a ≡ g ∘ a ∷ G [ a ])
  --        → Γ ⊩ f ≡ g ∷ A


  --  (p q : Γ ⊩⁰ A) → Γ ⊩⁰ A ≡ B / p → Γ ⊩⁰ A ≡ B / q
