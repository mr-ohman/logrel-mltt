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

record ne[_]_≡_[_] (Γ : Con Term) (A B K : Term) : Set where
  constructor ne[_,_,_,_]
  field
    M   : Term
    D'  : Γ ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ ⊢ K ≡ M

record ℕ[_]_∷_ (Γ : Con Term) (t A : Term) : Set where
  constructor ℕ[_,_,_]
  field
    n    : Term
    d    : Γ ⊢ t :⇒*: n ∷ ℕ
    natN : Natural n

record ℕ[_]_≡_∷_ (Γ : Con Term) (t u A : Term) : Set where
  constructor ℕ≡[_,_,_,_,_,_]
  field
    k      : Term
    k'     : Term
    d      : Γ ⊢ t ⇒* k  ∷ ℕ
    d'     : Γ ⊢ u ⇒* k' ∷ ℕ
    t≡u    : Γ ⊢ t ≡ u ∷ ℕ
    [k≡k'] : [Natural] (λ n n' → Γ ⊢ n ≡ n' ∷ ℕ) k k'

mutual
  -- split into small and big types ⊩⁰, ⊩¹
  -- toSubst : Wk -> Subst
  -- maybe define something like [_,_] : Subst -> Term -> Term; [ s , t ] = subst (consSubst s t)


  -- Helping functions for logical relation

  wk-prop⁰ : (Γ : Con Term) (F : Term) → Set
  wk-prop⁰ Γ F = ∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⁰ wkₜ ρ F

  wk-subst-prop⁰ : (Γ : Con Term) (F G : Term) ([F] : wk-prop⁰ Γ F) → Set
  wk-subst-prop⁰ Γ F G [F] = ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                                    → Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ → Δ ⊩⁰ wkLiftₜ ρ G [ a ]

  wk-substEq-prop⁰ : (Γ : Con Term) (F G : Term)
                    ([F] : wk-prop⁰ Γ F) ([G] : wk-subst-prop⁰ Γ F G [F]) → Set
  wk-substEq-prop⁰ Γ F G [F] [G] =
    ∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
              → Δ ⊩⁰ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ
              → Δ ⊩⁰ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G [ b ] / [G] ρ ⊢Δ [a]

  wk-fun-ext-prop⁰ : (Γ : Con Term) (F G f : Term)
                    ([F] : wk-prop⁰ Γ F) ([G] : wk-subst-prop⁰ Γ F G [F]) → Set
  wk-fun-ext-prop⁰ Γ F G f [F] [G] = ∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                   ([a≡b] : Δ ⊩⁰ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩⁰ wkₜ ρ f ∘ a ≡ wkₜ ρ f ∘ b ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a]

  data _⊩⁰_ (Γ : Con Term) : Term → Set where
    ℕ  : ∀ {A} (D : Γ ⊢ A :⇒*: ℕ) → Γ ⊩⁰ A
    ne : ∀ {A K} (D : Γ ⊢ A :⇒*: K) (neK : Neutral K) → Γ ⊩⁰ A
    Π  : ∀ {F G A} (D : Γ ⊢ A :⇒*: Π F ▹ G) (⊢F : Γ ⊢ F) (⊢G : Γ ∙ F ⊢ G)
                   ([F] : wk-prop⁰ Γ F) ([G] : wk-subst-prop⁰ Γ F G [F])
                   (G-ext : wk-substEq-prop⁰ Γ F G [F] [G]) → Γ ⊩⁰ A

  _⊩⁰_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ A ≡ B / ℕ  D = Γ ⊢ B ⇒* ℕ
  Γ ⊩⁰ A ≡ B / ne {K = K} D neK = ne[ Γ ] A ≡ B [ K ]
  Γ ⊩⁰ A ≡ B / Π  {F} {G} D ⊢F ⊢G [F] [G] G-ext = Π⁰[ Γ ] A ≡ B [ F , G , [F] , [G] ]

  _⊩⁰_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ t ∷ A / ℕ x = ℕ[ Γ ] t ∷ A
  Γ ⊩⁰ t ∷ A / ne x x₁ = Γ ⊢ t ∷ A
  Γ ⊩⁰ f ∷ A / Π {F} {G} D ⊢F ⊢G [F] [G] G-ext =
    Γ ⊢ f ∷ A × wk-fun-ext-prop⁰ Γ F G f [F] [G]

  _⊩⁰_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩⁰ A → Set
  Γ ⊩⁰ t ≡ u ∷ A / ℕ x = ℕ[ Γ ] t ≡ u ∷ A
  Γ ⊩⁰ t ≡ u ∷ A / ne x x₁ = Γ ⊢ t ≡ u ∷ A
  Γ ⊩⁰ t ≡ u ∷ A / Π {F} {G} x x₁ x₂ [F] [G] x₃ = --Π⁰ₜ[ Γ ] t ≡ u ∷ A [ F , G , Π x x₁ x₂ [F] [G] x₃ , [F] , [G] ]
    let [A] = Π x x₁ x₂ [F] [G] x₃
    in  Γ ⊩⁰ t ∷ A / [A]
    ×   Γ ⊩⁰ u ∷ A / [A]
    ×   Γ ⊢ t ≡ u ∷ A
    ×   (∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩⁰ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])

  -- Records for logical relation cases

  record Π⁰[_]_≡_[_,_,_,_] (Γ : Con Term) (A B F G : Term) ([F] : wk-prop⁰ Γ F)
                          ([G] : wk-subst-prop⁰ Γ F G [F]) : Set where
    inductive
    constructor Π⁰[_,_,_,_,_,_,_,_]
    field
      F'     : Term
      G'     : Term
      D'     : Γ ⊢ B ⇒* Π F' ▹ G'
      A≡B    : Γ ⊢ A ≡ B
      ⊩A     : Γ ⊩⁰ A
      ⊩B     : Γ ⊩⁰ B
      [F≡F'] : ∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⁰ wkₜ ρ F ≡ wkₜ ρ F' / [F] ρ ⊢Δ
      [G≡G'] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                       → Δ ⊩⁰ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G' [ a ] / [G] ρ ⊢Δ [a]

  -- Issue: Agda complains about record use not being strictly positive
  record Π⁰ₜ[_]_≡_∷_[_,_,_,_,_] (Γ : Con Term) (t u A F G : Term) ([A] : Γ ⊩⁰ A)
                              ([F] : wk-prop⁰ Γ F) ([G] : wk-subst-prop⁰ Γ F G [F]) : Set where
    inductive
    constructor Π⁰ₜ[_,_,_,_]
    field
      t≡u   : Γ ⊢ t ≡ u ∷ A
      ⊩t    : Γ ⊩⁰ t ∷ A / [A]
      ⊩u    : Γ ⊩⁰ u ∷ A / [A]
      [t≡u] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩⁰ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                      → Δ ⊩⁰ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a]



record U[_]_≡_∷_ (Γ : Con Term) (t u A : Term) : Set where
  constructor U[_,_,_,_,_,_]
  field
    ⊢t    : Γ ⊢ t ∷ U
    ⊢u    : Γ ⊢ u ∷ U
    t≡u   : Γ ⊢ t ≡ u ∷ U
    ⊩t    : Γ ⊩⁰ t
    ⊩u    : Γ ⊩⁰ u
    [t≡u] : Γ ⊩⁰ t ≡ u / ⊩t

mutual
  -- Helping functions for logical relation

  wk-prop¹ : (Γ : Con Term) (F : Term) → Set
  wk-prop¹ Γ F = ∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩¹ wkₜ ρ F

  wk-subst-prop¹ : (Γ : Con Term) (F G : Term) ([F] : wk-prop¹ Γ F) → Set
  wk-subst-prop¹ Γ F G [F] = ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                                    → Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ → Δ ⊩¹ wkLiftₜ ρ G [ a ]

  wk-substEq-prop¹ : (Γ : Con Term) (F G : Term)
                    ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F]) → Set
  wk-substEq-prop¹ Γ F G [F] [G] =
    ∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ
              → Δ ⊩¹ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G [ b ] / [G] ρ ⊢Δ [a]

  wk-fun-ext-prop¹ : (Γ : Con Term) (F G f : Term)
                    ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F]) → Set
  wk-fun-ext-prop¹ Γ F G f [F] [G] = ∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                   ([a≡b] : Δ ⊩¹ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩¹ wkₜ ρ f ∘ a ≡ wkₜ ρ f ∘ b ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a]

  data _⊩¹_ (Γ : Con Term) : Term → Set where
    U  : Γ ⊩¹ U
    ℕ  : Γ ⊩¹ ℕ
    Π  : ∀ {F G} (⊢F : Γ ⊢ F) (⊢G : Γ ∙ F ⊢ G) (⊩F : Γ ⊩¹ F)
                 ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F])
                 (G-ext : wk-substEq-prop¹ Γ F G [F] [G]) → Γ ⊩¹ Π F ▹ G
    emb : ∀ {A} → Γ ⊩⁰ A → Γ ⊩¹ A

  _⊩¹_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩¹ A → Set
  Γ ⊩¹ .U ≡ t / U = t PE.≡ U
  Γ ⊩¹ .ℕ ≡ t / ℕ = Γ ⊢ t ⇒* ℕ
  Γ ⊩¹ .(Π F ▹ G) ≡ t / Π {F} {G} ⊢F ⊢G D [F] [G] G-ext =
    Π¹[ Γ ] Π F ▹ G ≡ t [ F , G , [F] , [G] ]
  Γ ⊩¹ A ≡ B / emb x = Γ ⊩⁰ A ≡ B / x

  _⊩¹_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩¹ A → Set
  Γ ⊩¹ A ∷ .U / U = Γ ⊢ A ∷ U × Γ ⊩⁰ A
  Γ ⊩¹ a ∷ .ℕ / ℕ = ℕ[ Γ ] a ∷ ℕ
  Γ ⊩¹ f ∷ .(Π F ▹ G) / Π {F} {G} ⊢F ⊢G D [F] [G] G-ext =
    Γ ⊢ f ∷ Π F ▹ G × wk-fun-ext-prop¹ Γ F G f [F] [G]
  Γ ⊩¹ t ∷ A / emb x = Γ ⊩⁰ t ∷ A / x

  _⊩¹_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩¹ A → Set
  Γ ⊩¹ t ≡ u ∷ .U / U = U[ Γ ] t ≡ u ∷ U
  Γ ⊩¹ t ≡ u ∷ .ℕ / ℕ = ℕ[ Γ ] t ≡ u ∷ ℕ
  Γ ⊩¹ t ≡ u ∷ .(Π F ▹ G) / Π {F} {G} x x₁ x₂ [F] [G] x₃ = --Π¹ₜ[ Γ ] t ≡ u ∷ Π F ▹ G [ F , G , Π x x₁ x₂ [F] [G] x₃ , [F] , [G] ]
    let [A] = Π x x₁ x₂ [F] [G] x₃
    in  Γ ⊩¹ t ∷ Π F ▹ G / [A]
    ×   Γ ⊩¹ u ∷ Π F ▹ G / [A]
    ×   Γ ⊢ t ≡ u ∷ Π F ▹ G
    ×   (∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩¹ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
  Γ ⊩¹ t ≡ u ∷ A / emb x = Γ ⊩⁰ t ≡ u ∷ A / x

  -- Records for logical relation cases

  record Π¹[_]_≡_[_,_,_,_] (Γ : Con Term) (A B F G : Term) ([F] : wk-prop¹ Γ F)
                          ([G] : wk-subst-prop¹ Γ F G [F]) : Set where
    inductive
    constructor Π¹[_,_,_,_,_,_]
    field
      F'        : Term
      G'        : Term
      D'        : Γ ⊢ B ⇒* Π F' ▹ G'
      ΠFG≡ΠF'G' : Term.Π F ▹ G PE.≡ Π F' ▹ G'
      [F≡F']    : ∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩¹ wkₜ ρ F ≡ wkₜ ρ F' / [F] ρ ⊢Δ
      [G≡G']    : ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                          → Δ ⊩¹ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G' [ a ] / [G] ρ ⊢Δ [a]

  -- Issue: Agda complains about record use not being strictly positive
  record Π¹ₜ[_]_≡_∷_[_,_,_,_,_] (Γ : Con Term) (t u A F G : Term) ([A] : Γ ⊩¹ A)
                              ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F]) : Set where
    inductive
    constructor Π¹ₜ[_,_,_,_]
    field
      t≡u   : Γ ⊢ t ≡ u ∷ A
      ⊩t    : Γ ⊩¹ t ∷ A / [A]
      ⊩u    : Γ ⊩¹ u ∷ A / [A]
      [t≡u] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                      → Δ ⊩¹ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a]


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
