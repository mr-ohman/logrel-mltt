{-# OPTIONS --no-positivity-check #-}
-- Temporary, should not be used with a final solution

module Definition.LogicalRelation where

open import Tools.Context
open import Definition.Untyped
open import Definition.Typed
open import Data.Product
import Relation.Binary.PropositionalEquality as PE

mutual
  -- split into small and big types ⊩⁰, ⊩¹
  -- toSubst : Wk -> Subst
  -- maybe define something like [_,_] : Subst -> Term -> Term; [ s , t ] = subst (consSubst s t)

  data _⊩⁰_ (Γ : Con Term) : Term → Set where
    -- Or should it be:
    -- U : ∀ {A} → Γ ⊢ A ⇒* U → Γ ⊩ A
    ℕ  : ∀ {A} → Γ ⊢ A ⇒* ℕ → Γ ⊩⁰ A
    ne : ∀ {A K} → Γ ⊢ A ⇒* K → Neutral K
         → Γ ⊢ K
         → Γ ⊩⁰ A
    Π  : ∀ {A F G} → Γ ⊢ A ⇒* Π F ▹ G
       → Γ ⊢ F
       → Γ ∙ F ⊢ G
       → ([F] : (∀ {Δ} → (ρ : Δ ⊆ Γ) → Δ ⊩⁰ wk (toWk ρ) F))
       → ([G] : ∀ {Δ a} → (ρ : Δ ⊆ Γ) → Δ ⊩⁰ a ∷ wk (toWk ρ) F / [F] ρ → Δ ⊩⁰ wk (lift (toWk ρ)) G [ a ])
       → (∀ {Δ a b} → (ρ : Δ ⊆ Γ) → ([a] : Δ ⊩⁰ a ∷ wk (toWk ρ) F / [F] ρ) →
                      Δ ⊩⁰ a ≡ b ∷ wk (toWk ρ) F / [F] ρ → Δ ⊩⁰ wk (lift (toWk ρ)) G [ a ] ≡ wk (lift (toWk ρ)) G [ b ] / [G] ρ [a])

       → Γ ⊩⁰ A

  _⊩⁰_≡_/_ : (Γ : Con Term) (B : Term) →  Term → Γ ⊩⁰ B → Set
  _⊩⁰_≡_/_ = {!!}

  _⊩⁰_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩⁰ A → Set
  _⊩⁰_≡_∷_/_ = {!!}

  _⊩⁰_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩⁰ A → Set
  _⊩⁰_∷_/_ = {!!}

mutual
  data _⊩_ (Γ : Con Term) : Term → Set where
    U  : Γ ⊩ U
    -- Or should it be:
    -- U : ∀ {A} → Γ ⊢ A ⇒* U → Γ ⊩ A
    ℕ  : Γ ⊩ ℕ

    Π  : ∀ {F G}
       → Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊩ F
       → ([F] : (∀ {Δ} → (ρ : Γ ⊆ Δ) → Δ ⊩ wk (toWk ρ) F))
       → ([G] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) → Δ ⊩ a ∷ wk (toWk ρ) F / [F] ρ → Δ ⊩ wk (lift (toWk ρ)) G [ a ])
       → (∀ {Δ a b} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩ a ∷ wk (toWk ρ) F / [F] ρ) →
                      Δ ⊩ a ≡ b ∷ wk (toWk ρ) F / [F] ρ → Δ ⊩ wk (lift (toWk ρ)) G [ a ] ≡ wk (lift (toWk ρ)) G [ b ] / [G] ρ [a])
       → Γ ⊩ Π F ▹ G
    emb : ∀ {A} → Γ ⊩⁰ A → Γ ⊩ A

  _⊩_≡_/_ : (Γ : Con Term) (B : Term) →  Term → Γ ⊩ B → Set
  Γ ⊩ .U ≡ t / U = t PE.≡ U
  Γ ⊩ .ℕ ≡ t / ℕ = t PE.≡ ℕ
  Γ ⊩ .(Π F ▹ G) ≡ t / Π {F} {G} ⊢F ⊢G D [F] [G] G-ext = ∃ \ F' → ∃ \ G' → Term.Π F ▹ G PE.≡ Π F' ▹ G' ×
              (∀ {Δ} (ρ : Γ ⊆ Δ) → Δ ⊩ wk (toWk ρ) F ≡ wk (toWk ρ)  F' / [F] ρ) ×
              ((∀ {Δ a} → (ρ : Γ ⊆ Δ) → ([a] : Δ ⊩ a ∷ wk (toWk ρ) F / [F] ρ) →
                          Δ ⊩ wk (lift (toWk ρ)) G [ a ] ≡ wk (lift (toWk ρ)) G' [ a ] / [G] ρ [a]))
  Γ ⊩ A ≡ t / emb x = Γ ⊩⁰ A ≡ t / x

  _⊩_∷_/_ : (Γ : Con Term) (t A : Term) →  Γ ⊩ A → Set
  _⊩_∷_/_ = {!!}

  _⊩_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩ A → Set
  _⊩_≡_∷_/_ = {!!}

  -- data _⊩_≡_ (Γ : Con Term) : (B : Term) → Term → Set where
  --   U  : Γ ⊩ U ≡ U
  --   ℕ  : ∀ {A B} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* ℕ → Γ ⊩ A ≡ B
  --   ne : ∀ {A B K M} → Γ ⊢ A ⇒* K → Γ ⊢ B ⇒* M → Neutral K → Neutral M →
  --        Γ ⊢ A ≡ B →
  --        Γ ⊩ A ≡ B
  --   Π  : ∀ {A B F G H E} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ B ⇒* Π H ▹ E
  --      → Γ ⊢ A ≡ B → Γ ⊩ A → Γ ⊩ B → Γ ⊩ F ≡ H
  --      → (∀ {Δ a} → Δ ⊆ Γ → Δ ⊩ a ∷ F → Δ ⊩ G [ a ] ≡ E [ a ])
  --      → Γ ⊩ A ≡ B

  -- data _⊩_∷_ (Γ : Con Term) : Term → Term → Set where
  --   U    : ∀ {A} → Γ ⊢ A ∷ U → Γ ⊩ A → Γ ⊩ A ∷ U
  --   ne   : ∀ {A K a} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊢ a ∷ A → Γ ⊩ a ∷ A
  --   ℕ-ñ  : ∀ {A a ñ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* ñ ∷ ℕ → Γ ⊩ a ∷ A -- TODO fix ñ
  --   ℕ-ne : ∀ {A a k} → Γ ⊢ A ⇒* ℕ → Γ ⊢ a ⇒* k ∷ ℕ → Neutral k → Γ ⊩ a ∷ A
  --   Π    : ∀ {A F G f} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ f ∷ A
  --        → (∀ {Δ a b} → Δ ⊆ Γ → Δ ⊩ a ≡ b ∷ F → Δ ⊩ f ∘ a ≡ f ∘ b ∷ G [ a ])
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
  --        → (∀ {Δ a} → Δ ⊆ Γ → Δ ⊩ a ∷ F → Δ ⊩ f ∘ a ≡ g ∘ a ∷ G [ a ])
  --        → Γ ⊩ f ≡ g ∷ A
