module Definition.LogicalRelation where

open import Tools.Context

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening

open import Data.Product
open import Data.Sum
open import Data.Unit
import Relation.Binary.PropositionalEquality as PE


-- Records for logical relation cases

record ne[_]_≡_[_] (Γ : Con Term) (A B K : Term) : Set where
  constructor ne[_,_,_,_]
  field
    M   : Term
    D'  : Γ ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ ⊢ K ≡ M

natural-prop : (Γ : Con Term) (n : Term) → Natural n → Set
natural-prop Γ .(suc n) (suc {n}) = Γ ⊢ n ∷ ℕ
natural-prop Γ .zero zero = ⊤
natural-prop Γ n (ne x) = Γ ⊢ n ∷ ℕ

record ℕ[_]_∷_ (Γ : Con Term) (t A : Term) : Set where
  constructor ℕ[_,_,_,_]
  field
    n    : Term
    d    : Γ ⊢ t :⇒*: n ∷ ℕ
    natN : Natural n
    prop : natural-prop Γ n natN

record ℕ[_]_≡_∷_ (Γ : Con Term) (t u A : Term) : Set where
  constructor ℕ≡[_,_,_,_,_,_]
  field
    k      : Term
    k'     : Term
    d      : Γ ⊢ t :⇒*: k  ∷ ℕ
    d'     : Γ ⊢ u :⇒*: k' ∷ ℕ
    t≡u    : Γ ⊢ t ≡ u ∷ ℕ
    [k≡k'] : [Natural] (λ n n' → Γ ⊢ n ≡ n' ∷ ℕ) k k'


data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

record LogRelKit : Set₁ where
  constructor Kit
  field
    _⊩_ : (Γ : Con Term) → Term → Set
    _⊩_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩ A → Set
    _⊩_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩ A → Set
    _⊩_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩ A → Set

    wk-prop' : (Γ : Con Term) (F : Term) → Set
    wk-subst-prop' : (Γ : Con Term) (F G : Term) ([F] : wk-prop' Γ F) → Set
    wk-substEq-prop' : (Γ : Con Term) (F G : Term)
                       ([F] : wk-prop' Γ F) ([G] : wk-subst-prop' Γ F G [F]) → Set

data _<_ : (i j : TypeLevel) -> Set where
  0<1 : ⁰ < ¹

module LogRel (l : TypeLevel) (rec : ∀ {l'} → l' < l → LogRelKit) where
  module Lower {l'} {l< : l' < l} = LogRelKit (rec l<)
  record U[_][_]_≡_∷_ {l'}(l'< : l' < l)(Γ : Con Term) (t u A : Term) : Set where
    constructor U[_,_,_,_,_,_]
    open LogRelKit (rec l'<)
    field
      ⊢t    : Γ ⊢ t ∷ U
      ⊢u    : Γ ⊢ u ∷ U
      t≡u   : Γ ⊢ t ≡ u ∷ U
      ⊩t    : Γ ⊩ t
      ⊩u    : Γ ⊩ u
      [t≡u] : Γ ⊩ t ≡ u / ⊩t

  mutual
    -- Helping functions for logical relation

    wk-prop¹ : (Γ : Con Term) (F : Term) → Set
    wk-prop¹ Γ F = ∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩¹ wkₜ ρ F

    wk-subst-prop¹ : (Γ : Con Term) (F G : Term) ([F] : wk-prop¹ Γ F) → Set
    wk-subst-prop¹ Γ F G [F] = ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                                      → Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ → Δ ⊩¹ wkLiftₜ ρ G [ a ]

    wk-subst-prop-T¹ : (Γ : Con Term) (F G : Term) ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F]) (t : Term) → Set
    wk-subst-prop-T¹ Γ F G [F] [G] t = ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                                      → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ) → Δ ⊩¹ wkₜ ρ t ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a]

    wk-substEq-prop¹ : (Γ : Con Term) (F G : Term)
                      ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F]) → Set
    wk-substEq-prop¹ Γ F G [F] [G] =
      ∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                → Δ ⊩¹ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ
                → Δ ⊩¹ wkLiftₜ ρ G [ a ] ≡ wkLiftₜ ρ G [ b ] / [G] ρ ⊢Δ [a]

    wk-fun-ext-prop¹ : (Γ : Con Term) (F G f : Term)
                      ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F]) → Set
    wk-fun-ext-prop¹ Γ F G f [F] [G] = ∀ {Δ a b} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                     ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                     ([b] : Δ ⊩¹ b ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                     ([a≡b] : Δ ⊩¹ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                   → Δ ⊩¹ wkₜ ρ f ∘ a ≡ wkₜ ρ f ∘ b ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a]

    data _⊩¹_ (Γ : Con Term) : Term → Set where
      U  : ∀ {l'} {l< : l' < l} (⊢Γ : ⊢ Γ) → Γ ⊩¹ U
      ℕ  : ∀ {A} (D : Γ ⊢ A :⇒*: ℕ) → Γ ⊩¹ A
      ne : ∀ {A K} (D : Γ ⊢ A :⇒*: K) (neK : Neutral K) → Γ ⊩¹ A
      Π  : ∀ {F G A} (D : Γ ⊢ A :⇒*: Π F ▹ G) (⊢F : Γ ⊢ F) (⊢G : Γ ∙ F ⊢ G)
                   ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F])
                   (G-ext : wk-substEq-prop¹ Γ F G [F] [G]) → Γ ⊩¹ A
      emb : ∀ {A l'}{l< : l' < l} (let open LogRelKit (rec l<))
                     → Γ ⊩ A  → Γ ⊩¹ A

    _⊩¹_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ .U ≡ t / U {l< = l<} ⊢Γ = t PE.≡ U
    Γ ⊩¹ A ≡ B / ℕ  D = Γ ⊢ B ⇒* ℕ
    Γ ⊩¹ A ≡ B / ne {K = K} D neK = ne[ Γ ] A ≡ B [ K ]
    Γ ⊩¹ A ≡ B / Π  {F} {G} D ⊢F ⊢G [F] [G] G-ext = Π¹[ Γ ] A ≡ B [ F , G , [F] , [G] ]
    Γ ⊩¹ A ≡ B / emb x = Γ Lower.⊩ A ≡ B / x

    _⊩¹_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ A ∷ .U / U {l< = l<} ⊢Γ = Γ ⊢ A ∷ U × Γ ⊩ A where open Lower {l< = l<}
    Γ ⊩¹ t ∷ A / ℕ x = ℕ[ Γ ] t ∷ A
    Γ ⊩¹ t ∷ A / ne x x₁ = Γ ⊢ t ∷ A
    Γ ⊩¹ f ∷ A / Π {F} {G} D ⊢F ⊢G [F] [G] G-ext =
      Γ ⊢ f ∷ A × wk-fun-ext-prop¹ Γ F G f [F] [G]
    Γ ⊩¹ t ∷ A / emb x = Γ Lower.⊩ t ∷ A / x

    _⊩¹_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ t ≡ u ∷ .U / U {l< = l<} ⊢Γ = U[ l< ][ Γ ] t ≡ u ∷ U
    Γ ⊩¹ t ≡ u ∷ A / ℕ x = ℕ[ Γ ] t ≡ u ∷ A
    Γ ⊩¹ t ≡ u ∷ A / ne x x₁ = Γ ⊢ t ≡ u ∷ A
    Γ ⊩¹ t ≡ u ∷ A / Π {F} {G} x x₁ x₂ [F] [G] x₃ = --Π¹ₜ[ Γ ] t ≡ u ∷ A [ F , G , Π x x₁ x₂ [F] [G] x₃ , [F] , [G] ]
      let [A] = Π x x₁ x₂ [F] [G] x₃
      in  Γ ⊢ t ≡ u ∷ A
      ×   Γ ⊩¹ t ∷ A / [A]
      ×   Γ ⊩¹ u ∷ A / [A]
      ×   (∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
                 → Δ ⊩¹ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
    Γ ⊩¹ t ≡ u ∷ A / emb x = Γ Lower.⊩ t ≡ u ∷ A / x

    record Π¹[_]_≡_[_,_,_,_] (Γ : Con Term) (A B F G : Term) ([F] : wk-prop¹ Γ F)
                            ([G] : wk-subst-prop¹ Γ F G [F]) : Set where
      inductive
      constructor Π¹[_,_,_,_,_,_]
      field
        F'     : Term
        G'     : Term
        D'     : Γ ⊢ B ⇒* Π F' ▹ G'
        A≡B    : Γ ⊢ A ≡ B
        -- ⊩A     : Γ ⊩⁰ A
        -- ⊩B     : Γ ⊩⁰ B
        [F≡F'] : ∀ {Δ} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩¹ wkₜ ρ F ≡ wkₜ ρ F' / [F] ρ ⊢Δ
        [G≡G'] : ∀ {Δ a} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩¹ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
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

    kit : LogRelKit
    kit = Kit _⊩¹_ _⊩¹_≡_/_ _⊩¹_∷_/_ _⊩¹_≡_∷_/_ wk-prop¹ wk-subst-prop¹ wk-substEq-prop¹

open LogRel public using (U; ℕ; ne; Π; emb; U[_,_,_,_,_,_]; Π¹[_,_,_,_,_,_]; Π¹ₜ[_,_,_,_])

logRelRec : ∀ l {l'} → l' < l → LogRelKit
logRelRec ⁰ = λ()
logRelRec ¹ 0<1 = LogRel.kit ⁰ (\ ())

kit : ∀ (i : TypeLevel) → LogRelKit
kit l = LogRel.kit l (logRelRec l)
-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for TypeLevel because you could recurse.

_⊩⟨_⟩_ : (Γ : Con Term) (T : TypeLevel) → Term → Set
Γ ⊩⟨ l ⟩ A  = Γ ⊩ A where open LogRelKit (kit l)

_⊩⟨_⟩_≡_/_ : (Γ : Con Term) (T : TypeLevel) (A B : Term) → Γ ⊩⟨ T ⟩ A → Set
Γ ⊩⟨ l ⟩ A ≡ B / [A] = Γ ⊩ A ≡ B / [A] where open LogRelKit (kit l)


_⊩⟨_⟩_∷_/_ : (Γ : Con Term) (T : TypeLevel) (t A : Term) → Γ ⊩⟨ T ⟩ A → Set
Γ ⊩⟨ l ⟩ t ∷ A / [A] = Γ ⊩ t ∷ A / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term) (T : TypeLevel) (t u A : Term) → Γ ⊩⟨ T ⟩ A → Set
Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] = Γ ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit l)

wk-prop : ∀ l (Γ : Con Term) (F : Term) → Set
wk-prop l = wk-prop' where open LogRelKit (kit l)

wk-subst-prop : ∀ l (Γ : Con Term) (F G : Term) ([F] : wk-prop l Γ F) → Set
wk-subst-prop l = wk-subst-prop' where open LogRelKit (kit l)

wk-substEq-prop : ∀ l (Γ : Con Term) (F G : Term)
                  ([F] : wk-prop l Γ F) ([G] : wk-subst-prop l Γ F G [F]) → Set
wk-substEq-prop l = wk-substEq-prop' where open LogRelKit (kit l)
