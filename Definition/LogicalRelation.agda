--{-# OPTIONS --no-positivity-check #-}
-- Temporary, should not be used with a final solution

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
  -- split into small and big types ⊩⁰, ⊩
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
       → ([F] : (∀ {Δ} → (ρ : Γ ⊆ Δ) → Δ ⊩⁰ wk (toWk ρ) F))
       → ([G] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) → Δ ⊩⁰ a ∷ wk (toWk ρ) F / [F] ρ → Δ ⊩⁰ wk (lift (toWk ρ)) G [ a ])
       → (∀ {Δ a b} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩⁰ a ∷ wk (toWk ρ) F / [F] ρ) →
                      Δ ⊩⁰ a ≡ b ∷ wk (toWk ρ) F / [F] ρ → Δ ⊩⁰ wk (lift (toWk ρ)) G [ a ] ≡ wk (lift (toWk ρ)) G [ b ] / [G] ρ [a])
       → Γ ⊩⁰ A



  _⊩⁰_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ A ≡ B / ℕ  A⇒*ℕ = Γ ⊢ B ⇒* ℕ
  Γ ⊩⁰ A ≡ B / ne A⇒*K neK ⊢K = ∃ λ M → Γ ⊢ B ⇒* M × Neutral M × Γ ⊢ M
  Γ ⊩⁰ A ≡ B / Π  {F} {G} D ⊢F ⊢G [F] [G] G-ext =
    ∃₂ λ F' G'
    → Γ ⊢ A ≡ B
    × Γ ⊩⁰ A
    × Γ ⊩⁰ B
    × (∀ {Δ} → (ρ : Γ ⊆ Δ) → Δ ⊩⁰ wk (toWk ρ) F ≡ wk (toWk ρ) F' / [F] ρ)
    × (∀ {Δ a} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩⁰ a ∷ wk (toWk ρ) F / [F] ρ)
               → Δ ⊩⁰ wk (lift (toWk ρ)) G [ a ] ≡ wk (lift (toWk ρ)) G' [ a ] / [G] ρ [a])

  _⊩⁰_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ t ∷ A / ℕ x = (∃ λ n → Γ ⊢ t ⇒* n ∷ ℕ × Natural n) -- ⊎ (∃ λ k → Γ ⊢ t ⇒* k ∷ ℕ × Neutral k)
  Γ ⊩⁰ t ∷ A / ne x x₁ x₂ = Γ ⊢ t ∷ A
  Γ ⊩⁰ f ∷ A / Π {F} {G} x x₁ x₂ [F] [G] x₃ = Γ ⊢ f ∷ A
    × (∀ {Δ a b} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩⁰ a ∷ wk (toWk ρ) F / [F] ρ)
                 → Δ ⊩⁰ a ≡ b ∷ wk (toWk ρ) F / [F] ρ
                 → Δ ⊩⁰ wk (toWk ρ) f ∘ a ≡ wk (toWk ρ) f ∘ b ∷ wk (lift (toWk ρ)) G [ a ] / [G] ρ [a])

  _⊩⁰_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ t ≡ u ∷ A / ℕ x = (∃₂ λ k k' → [Natural] (\ n n' → Γ ⊢ n ≡ n' ∷ ℕ) k k' × Γ ⊢ t ⇒* k ∷ ℕ × Γ ⊢ u ⇒* k' ∷ ℕ × Γ ⊢ t ≡ u ∷ ℕ)
  Γ ⊩⁰ t ≡ u ∷ A / ne x x₁ x₂ = Γ ⊢ t ≡ u ∷ A
  Γ ⊩⁰ t ≡ u ∷ A / Π {F} {G} x x₁ x₂ [F] [G] x₃ =
    let [A] = Π x x₁ x₂ [F] [G] x₃
    in  Γ ⊩⁰ t ∷ A / [A]
    ×   Γ ⊩⁰ u ∷ A / [A]
    ×   Γ ⊢ t ≡ u ∷ A
    ×   (∀ {Δ a} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩⁰ a ∷ wk (toWk ρ) F / [F] ρ)
                 → Δ ⊩⁰ wk (toWk ρ) t ∘ a ≡ wk (toWk ρ) u ∘ a ∷ wk (lift (toWk ρ)) G [ a ] / [G] ρ [a])

mutual
  data _⊩_ (Γ : Con Term) : Term → Set where
    U  : Γ ⊩ U
    ℕ  : Γ ⊩ ℕ
    Π  : ∀ {F G}
       → Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊩ F
       → ([F] : (∀ {Δ} → (ρ : Γ ⊆ Δ) → Δ ⊩ wk (toWk ρ) F))
       → ([G] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) → Δ ⊩ a ∷ wk (toWk ρ) F / [F] ρ → Δ ⊩ wk (lift (toWk ρ)) G [ a ])
       → (∀ {Δ a b} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩ a ∷ wk (toWk ρ) F / [F] ρ)
                    → Δ ⊩ a ≡ b ∷ wk (toWk ρ) F / [F] ρ → Δ ⊩ wk (lift (toWk ρ)) G [ a ] ≡ wk (lift (toWk ρ)) G [ b ] / [G] ρ [a])
       → Γ ⊩ Π F ▹ G
    emb : ∀ {A} → Γ ⊩⁰ A → Γ ⊩ A

  _⊩_≡_/_ : (Γ : Con Term) (B : Term) → Term → Γ ⊩ B → Set
  Γ ⊩ .U ≡ t / U = t PE.≡ U
  Γ ⊩ .ℕ ≡ t / ℕ = t PE.≡ ℕ
  Γ ⊩ .(Π F ▹ G) ≡ t / Π {F} {G} ⊢F ⊢G D [F] [G] G-ext = ∃₂ λ F' G' → Term.Π F ▹ G PE.≡ Π F' ▹ G' ×
              (∀ {Δ} (ρ : Γ ⊆ Δ) → Δ ⊩ wk (toWk ρ) F ≡ wk (toWk ρ)  F' / [F] ρ) ×
              ((∀ {Δ a} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩ a ∷ wk (toWk ρ) F / [F] ρ) →
                          Δ ⊩ wk (lift (toWk ρ)) G [ a ] ≡ wk (lift (toWk ρ)) G' [ a ] / [G] ρ [a]))
  Γ ⊩ A ≡ B / emb x = Γ ⊩⁰ A ≡ B / x

  _⊩_∷_/_ : (Γ : Con Term) (t A : Term) →  Γ ⊩ A → Set
  Γ ⊩ A ∷ .U / U = Γ ⊢ A ∷ U × Γ ⊩⁰ A
  Γ ⊩ a ∷ .ℕ / ℕ = (∃ λ n → Γ ⊢ a ⇒* n ∷ ℕ × Natural n) ⊎ (∃ λ k → Γ ⊢ a ⇒* k ∷ ℕ × Neutral k)
  Γ ⊩ f ∷ .(Π F ▹ G) / Π {F} {G} ⊢F ⊢G D [F] [G] G-ext = Γ ⊢ f ∷ Π F ▹ G
    × (∀ {Δ a b} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩ a ∷ wk (toWk ρ) F / [F] ρ)
                 → Δ ⊩ a ≡ b ∷ wk (toWk ρ) F / [F] ρ
                 → Δ ⊩ wk (toWk ρ) f ∘ a ≡ wk (toWk ρ) f ∘ b ∷ wk (lift (toWk ρ)) G [ a ] / [G] ρ [a])
  Γ ⊩ t ∷ A / emb x = Γ ⊩⁰ t ∷ A / x

  _⊩_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩ A → Set
  Γ ⊩ t ≡ u ∷ .U / U = Γ ⊢ t ∷ U × Γ ⊢ u ∷ U × Γ ⊩⁰ u × Σ (Γ ⊩⁰ t) (λ t₀ → Γ ⊩⁰ t ≡ u / t₀)
  Γ ⊩ t ≡ u ∷ .ℕ / ℕ = (∃ λ n → Natural n × Γ ⊢ t ⇒* n ∷ ℕ × Γ ⊢ u ⇒* n ∷ ℕ)
                       ⊎ (∃₂ λ k k' → Neutral k × Neutral k' × Γ ⊢ t ⇒* k ∷ ℕ × Γ ⊢ u ⇒* k' ∷ ℕ × Γ ⊢ t ≡ u ∷ ℕ)
  Γ ⊩ t ≡ u ∷ .(Π F ▹ G) / Π {F} {G} x x₁ x₂ [F] [G] x₃ =
    let [A] = Π x x₁ x₂ [F] [G] x₃
    in  Γ ⊩ t ∷ Π F ▹ G / [A]
    ×   Γ ⊩ u ∷ Π F ▹ G / [A]
    ×   Γ ⊢ t ≡ u ∷ Π F ▹ G
    ×   (∀ {Δ a} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩ a ∷ wk (toWk ρ) F / [F] ρ)
                 → Δ ⊩ wk (toWk ρ) t ∘ a ≡ wk (toWk ρ) u ∘ a ∷ wk (lift (toWk ρ)) G [ a ] / [G] ρ [a])
  Γ ⊩ t ≡ u ∷ A / emb x = Γ ⊩⁰ t ≡ u ∷ A / x

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
