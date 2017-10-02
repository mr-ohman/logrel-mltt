{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening

open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE


-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as sound.

-- Soundness of Neutrals:

-- Neutral type
record _⊩ne_ (Γ : Con Term) (A : Term) : Set where
  constructor ne
  field
    K   : Term
    D   : Γ ⊢ A :⇒*: K
    neK : Neutral K
    K≡K : Γ ⊢ K ~ K ∷ U

-- Neutral type equality
record _⊩ne_≡_/_ (Γ : Con Term) (A B : Term) ([A] : Γ ⊩ne A) : Set where
  constructor ne₌
  open _⊩ne_ [A]
  field
    M   : Term
    D′  : Γ ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ ⊢ K ~ M ∷ U

-- Neutral term in WHNF
record _⊩neNf_∷_ (Γ : Con Term) (k A : Term) : Set where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ ⊢ k ∷ A
    k≡k  : Γ ⊢ k ~ k ∷ A

-- Neutral term
record _⊩ne_∷_/_ (Γ : Con Term) (t A : Term) ([A] : Γ ⊩ne A) : Set where
  inductive
  constructor neₜ
  open _⊩ne_ [A]
  field
    k   : Term
    d   : Γ ⊢ t :⇒*: k ∷ K
    nf  : Γ ⊩neNf k ∷ K

-- Neutral term equality in WHNF
record _⊩neNf_≡_∷_ (Γ : Con Term) (k m A : Term) : Set where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ ⊢ k ~ m ∷ A

-- Neutral term equality
record _⊩ne_≡_∷_/_ (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩ne A) : Set where
  constructor neₜ₌
  open _⊩ne_ [A]
  field
    k m : Term
    d   : Γ ⊢ t :⇒*: k ∷ K
    d′  : Γ ⊢ u :⇒*: m ∷ K
    nf  : Γ ⊩neNf k ≡ m ∷ K

-- Soundness of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩ℕ A = Γ ⊢ A :⇒*: ℕ

-- Natural number type equality
_⊩ℕ_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩ℕ A ≡ B = Γ ⊢ B ⇒* ℕ

mutual
  -- Natural number term
  data _⊩ℕ_∷ℕ (Γ : Con Term) (t : Term) : Set where
    ℕₜ : (n : Term) (d : Γ ⊢ t :⇒*: n ∷ ℕ) (n≡n : Γ ⊢ n ≅ n ∷ ℕ)
         (prop : Natural-prop Γ n)
       → Γ ⊩ℕ t ∷ℕ

  -- Natural number term WHNF property
  data Natural-prop (Γ : Con Term) : (n : Term) → Set where
    suc  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    zero : Natural-prop Γ zero
    ne   : ∀ {n} → Γ ⊩neNf n ∷ ℕ → Natural-prop Γ n

mutual
  -- Natural number term equality
  data _⊩ℕ_≡_∷ℕ (Γ : Con Term) (t u : Term) : Set where
    ℕₜ₌ : (k k′ : Term) (d : Γ ⊢ t :⇒*: k  ∷ ℕ) (d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ)
          (k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ)
          (prop : [Natural]-prop Γ k k′) → Γ ⊩ℕ t ≡ u ∷ℕ

  -- Natural number term equality WHNF property
  data [Natural]-prop (Γ : Con Term) : (n n′ : Term) → Set where
    suc : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zero : [Natural]-prop Γ zero zero
    ne : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ n n′

-- Natural extraction from term WHNF property
natural : ∀ {Γ n} → Natural-prop Γ n → Natural n
natural (suc x) = suc
natural zero = zero
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Natural extraction from term equality WHNF property
split : ∀ {Γ a b} → [Natural]-prop Γ a b → Natural a × Natural b
split (suc x) = suc , suc
split zero = zero , zero
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM


-- Type levels

data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

data _<_ : (i j : TypeLevel) → Set where
  0<1 : ⁰ < ¹

-- Logical relation

record LogRelKit : Set₁ where
  constructor Kit
  field
    _⊩U : (Γ : Con Term) → Set
    _⊩Π_ : (Γ : Con Term) → Term → Set

    _⊩_ : (Γ : Con Term) → Term → Set
    _⊩_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩ A → Set
    _⊩_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩ A → Set
    _⊩_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩ A → Set

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ < l → LogRelKit) where

  -- Soundness of Universe:

  -- Universe type
  record _⊩¹U (Γ : Con Term) : Set where
    constructor U
    field
      l′ : TypeLevel
      l< : l′ < l
      ⊢Γ : ⊢ Γ

  -- Universe type equality
  _⊩¹U≡_ : (Γ : Con Term) (B : Term) → Set
  Γ ⊩¹U≡ B = B PE.≡ U

  -- Universe term
  record _⊩¹U_∷U/_ {l′} (Γ : Con Term) (t : Term) (l< : l′ < l) : Set where
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term
      d     : Γ ⊢ t :⇒*: A ∷ U
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ U
      [t]   : Γ ⊩ t

  -- Universe term equality
  record _⊩¹U_≡_∷U/_ {l′} (Γ : Con Term) (t u : Term) (l< : l′ < l) : Set where
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term
      d     : Γ ⊢ t :⇒*: A ∷ U
      d′    : Γ ⊢ u :⇒*: B ∷ U
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ U
      [t]   : Γ ⊩ t
      [u]   : Γ ⊩ u
      [t≡u] : Γ ⊩ t ≡ u / [t]

  mutual

    -- Soundness of Π:

    -- Π-type
    record _⊩¹Π_ (Γ : Con Term) (A : Term) : Set where
      inductive
      constructor Π
      field
        F : Term
        G : Term
        D : Γ ⊢ A :⇒*: Π F ▹ G
        ⊢F : Γ ⊢ F
        ⊢G : Γ ∙ F ⊢ G
        A≡A : Γ ⊢ Π F ▹ G ≅ Π F ▹ G
        [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ F
        [G] : ∀ {ρ Δ a}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ ⊩¹ U.wk (lift ρ) G [ a ]
        G-ext : ∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
              → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a]

    -- Π-type equality
    record _⊩¹Π_≡_/_ (Γ : Con Term) (A B : Term) ([A] : Γ ⊩¹Π A) : Set where
      inductive
      constructor Π₌
      open _⊩¹Π_ [A]
      field
        F′     : Term
        G′     : Term
        D′     : Γ ⊢ B ⇒* Π F′ ▹ G′
        A≡B    : Γ ⊢ Π F ▹ G ≅ Π F′ ▹ G′
        [F≡F′] : ∀ {ρ Δ}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩¹ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {ρ Δ a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] / [G] [ρ] ⊢Δ [a]

    -- Term of Π-type
    _⊩¹Π_∷_/_ : (Γ : Con Term) (t A : Term) ([A] : Γ ⊩¹Π A) → Set
    Γ ⊩¹Π t ∷ A / Π F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π F ▹ G
            × Function f
            × Γ ⊢ f ≅ f ∷ Π F ▹ G
            × (∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                ([b] : Δ ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
            × (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×


    -- Term equality of Π-type
    _⊩¹Π_≡_∷_/_ : (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩¹Π A) → Set
    Γ ⊩¹Π t ≡ u ∷ A / Π F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      let [A] = Π F G D ⊢F ⊢G A≡A [F] [G] G-ext
      in  ∃₂ λ f g →
          Γ ⊢ t :⇒*: f ∷ Π F ▹ G
      ×   Γ ⊢ u :⇒*: g ∷ Π F ▹ G
      ×   Function f
      ×   Function g
      ×   Γ ⊢ f ≅ g ∷ Π F ▹ G
      ×   Γ ⊩¹Π t ∷ A / [A]
      ×   Γ ⊩¹Π u ∷ A / [A]
      ×   (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
          → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.


    -- Logical relation definition

    data _⊩¹_ (Γ : Con Term) : Term → Set where
      U  : Γ ⊩¹U → Γ ⊩¹ U
      ℕ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩¹ A
      ne : ∀ {A} → Γ ⊩ne A → Γ ⊩¹ A
      Π  : ∀ {A} → Γ ⊩¹Π A → Γ ⊩¹ A
      emb : ∀ {A l′} (l< : l′ < l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A) → Γ ⊩¹ A

    _⊩¹_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ .U ≡ B / U UA = Γ ⊩¹U≡ B
    Γ ⊩¹ A ≡ B / ℕ D = Γ ⊩ℕ A ≡ B
    Γ ⊩¹ A ≡ B / ne neA = Γ ⊩ne A ≡ B / neA
    Γ ⊩¹ A ≡ B / Π ΠA = Γ ⊩¹Π A ≡ B / ΠA
    Γ ⊩¹ A ≡ B / emb l< [A] = Γ ⊩ A ≡ B / [A]
      where open LogRelKit (rec l<)

    _⊩¹_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ t ∷ .U / U (U l′ l< ⊢Γ) = Γ ⊩¹U t ∷U/ l<
    Γ ⊩¹ t ∷ A / ℕ D = Γ ⊩ℕ t ∷ℕ
    Γ ⊩¹ t ∷ A / ne neA = Γ ⊩ne t ∷ A / neA
    Γ ⊩¹ f ∷ A / Π ΠA  = Γ ⊩¹Π f ∷ A / ΠA
    Γ ⊩¹ t ∷ A / emb l< [A] = Γ ⊩ t ∷ A / [A]
      where open LogRelKit (rec l<)

    _⊩¹_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ t ≡ u ∷ .U / U (U l′ l< ⊢Γ) = Γ ⊩¹U t ≡ u ∷U/ l<
    Γ ⊩¹ t ≡ u ∷ A / ℕ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩¹ t ≡ u ∷ A / ne neA = Γ ⊩ne t ≡ u ∷ A / neA
    Γ ⊩¹ t ≡ u ∷ A / Π ΠA = Γ ⊩¹Π t ≡ u ∷ A / ΠA
    Γ ⊩¹ t ≡ u ∷ A / emb l< [A] = Γ ⊩ t ≡ u ∷ A / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩¹U _⊩¹Π_
              _⊩¹_ _⊩¹_≡_/_ _⊩¹_∷_/_ _⊩¹_≡_∷_/_

open LogRel public using (U; ℕ; ne; Π; emb; Uₜ; Uₜ₌; Π₌)

-- Patterns for the non-records of Π
pattern Πₜ a b c d e f = a , b , c , d , e , f
pattern Πₜ₌ a b c d e f g h i j = a , b , c , d , e , f , g , h , i , j

pattern U′  a b c = U (U a b c)
pattern ne′ a b c d = ne (ne a b c d)
pattern Π′  a b c d e f g h i = Π (Π a b c d e f g h i)

logRelRec : ∀ l {l′} → l′ < l → LogRelKit
logRelRec ⁰ = λ ()
logRelRec ¹ 0<1 = LogRel.kit ⁰ (λ ())

kit : ∀ (i : TypeLevel) → LogRelKit
kit l = LogRel.kit l (logRelRec l)
-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

_⊩′⟨_⟩U : (Γ : Con Term) (l : TypeLevel) → Set
Γ ⊩′⟨ l ⟩U = Γ ⊩U where open LogRelKit (kit l)

_⊩′⟨_⟩Π_ : (Γ : Con Term) (l : TypeLevel) → Term → Set
Γ ⊩′⟨ l ⟩Π A = Γ ⊩Π A where open LogRelKit (kit l)

_⊩⟨_⟩_ : (Γ : Con Term) (l : TypeLevel) → Term → Set
Γ ⊩⟨ l ⟩ A = Γ ⊩ A where open LogRelKit (kit l)

_⊩⟨_⟩_≡_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) → Γ ⊩⟨ l ⟩ A → Set
Γ ⊩⟨ l ⟩ A ≡ B / [A] = Γ ⊩ A ≡ B / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_∷_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) → Γ ⊩⟨ l ⟩ A → Set
Γ ⊩⟨ l ⟩ t ∷ A / [A] = Γ ⊩ t ∷ A / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) → Γ ⊩⟨ l ⟩ A → Set
Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] = Γ ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit l)
