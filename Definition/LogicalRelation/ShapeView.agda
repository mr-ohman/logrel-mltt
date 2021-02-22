{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.ShapeView {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Reflexivity

open import Tools.Nat
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B : Term n

-- Type for maybe embeddings of reducible types
data MaybeEmb (l : TypeLevel) (⊩⟨_⟩ : TypeLevel → Set) : Set where
  noemb : ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : ∀ {l′} → l′ < l → MaybeEmb l′ ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

-- Specific reducible types with possible embedding

_⊩⟨_⟩U : (Γ : Con Term n) (l : TypeLevel) → Set
Γ ⊩⟨ l ⟩U = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U)

_⊩⟨_⟩ℕ_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩Empty_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set
Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

_⊩⟨_⟩Unit_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set
Γ ⊩⟨ l ⟩Unit A = MaybeEmb l (λ l′ → Γ ⊩Unit A)

_⊩⟨_⟩ne_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set
Γ ⊩⟨ l ⟩ne A = MaybeEmb l (λ l′ → Γ ⊩ne A)

_⊩⟨_⟩B⟨_⟩_ : (Γ : Con Term n) (l : TypeLevel) (W : BindingType) (A : Term n) → Set
Γ ⊩⟨ l ⟩B⟨ W ⟩ A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ A)

-- Construct a general reducible type from a specific

U-intr : ∀ {l} → Γ ⊩⟨ l ⟩U → Γ ⊩⟨ l ⟩ U
U-intr (noemb x) = Uᵣ x
U-intr (emb 0<1 x) = emb 0<1 (U-intr x)

ℕ-intr : ∀ {A l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb 0<1 x) = emb 0<1 (ℕ-intr x)

Empty-intr : ∀ {A l} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr (emb 0<1 x) = emb 0<1 (Empty-intr x)

Unit-intr : ∀ {A l} → Γ ⊩⟨ l ⟩Unit A → Γ ⊩⟨ l ⟩ A
Unit-intr (noemb x) = Unitᵣ x
Unit-intr (emb 0<1 x) = emb 0<1 (Unit-intr x)

ne-intr : ∀ {A l} → Γ ⊩⟨ l ⟩ne A → Γ ⊩⟨ l ⟩ A
ne-intr (noemb x) = ne x
ne-intr (emb 0<1 x) = emb 0<1 (ne-intr x)

B-intr : ∀ {A l} W → Γ ⊩⟨ l ⟩B⟨ W ⟩ A → Γ ⊩⟨ l ⟩ A
B-intr W (noemb x) = Bᵣ W x
B-intr W (emb 0<1 x) = emb 0<1 (B-intr W x)

-- Construct a specific reducible type from a general with some criterion

U-elim : ∀ {l} → Γ ⊩⟨ l ⟩ U → Γ ⊩⟨ l ⟩U
U-elim (Uᵣ′ l′ l< ⊢Γ) = noemb (Uᵣ l′ l< ⊢Γ)
U-elim (ℕᵣ D) with whnfRed* (red D) Uₙ
... | ()
U-elim (Emptyᵣ D) with whnfRed* (red D) Uₙ
... | ()
U-elim (Unitᵣ D) with whnfRed* (red D) Uₙ
... | ()
U-elim (ne′ K D neK K≡K) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-elim (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
U-elim (emb 0<1 x) with U-elim x
U-elim (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
U-elim (emb 0<1 x) | emb () x₁

ℕ-elim′ : ∀ {A l} → Γ ⊢ A ⇒* ℕ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ l′ l< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ℕₙ)
... | ()
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢B W (whrDet* (D , ℕₙ) (red D′ , ⟦ W ⟧ₙ)))
ℕ-elim′ D (Emptyᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Emptyₙ)
... | ()
ℕ-elim′ D (Unitᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Unitₙ)
... | ()
ℕ-elim′ D (emb 0<1 x) with ℕ-elim′ D x
ℕ-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim′ D (emb 0<1 x) | emb () x₂

ℕ-elim : ∀ {l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

Empty-elim′ : ∀ {A l} → Γ ⊢ A ⇒* Empty → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Uᵣ′ l′ l< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Emptyₙ)
... | ()
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (Unitᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , Unitₙ)
... | ()
Empty-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢B W (whrDet* (D , Emptyₙ) (red D′ , ⟦ W ⟧ₙ)))
Empty-elim′ D (ℕᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , ℕₙ)
... | ()
Empty-elim′ D (emb 0<1 x) with Empty-elim′ D x
Empty-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Empty-elim′ D (emb 0<1 x) | emb () x₂

Empty-elim : ∀ {l} → Γ ⊩⟨ l ⟩ Empty → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

Unit-elim′ : ∀ {A l} → Γ ⊢ A ⇒* Unit → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Unit A
Unit-elim′ D (Uᵣ′ l′ l< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Unitₙ)
... | ()
Unit-elim′ D (Unitᵣ D′) = noemb D′
Unit-elim′ D (Emptyᵣ D′) with whrDet* (D , Unitₙ) (red D′ , Emptyₙ)
... | ()
Unit-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (red D′ , ne neK)))
Unit-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Unit≢B W (whrDet* (D , Unitₙ) (red D′ , ⟦ W ⟧ₙ)))
Unit-elim′ D (ℕᵣ D′) with whrDet* (D , Unitₙ) (red D′ , ℕₙ)
... | ()
Unit-elim′ D (emb 0<1 x) with Unit-elim′ D x
Unit-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Unit-elim′ D (emb 0<1 x) | emb () x₂

Unit-elim : ∀ {l} → Γ ⊩⟨ l ⟩ Unit → Γ ⊩⟨ l ⟩Unit Unit
Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

ne-elim′ : ∀ {A l K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ne A
ne-elim′ D neK (Uᵣ′ l′ l< ⊢Γ) =
  ⊥-elim (U≢ne neK (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (Unitᵣ D′) = ⊥-elim (Unit≢ne neK (whrDet* (red D′ , Unitₙ) (D , ne neK)))
ne-elim′ D neK (ne′ K D′ neK′ K≡K) = noemb (ne K D′ neK′ K≡K)
ne-elim′ D neK (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (B≢ne W neK (whrDet* (red D′ , ⟦ W ⟧ₙ) (D , ne neK)))
ne-elim′ D neK (emb 0<1 x) with ne-elim′ D neK x
ne-elim′ D neK (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ne-elim′ D neK (emb 0<1 x) | emb () x₂

ne-elim : ∀ {l K} → Neutral K  → Γ ⊩⟨ l ⟩ K → Γ ⊩⟨ l ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

B-elim′ : ∀ {A F G l} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩B⟨ W ⟩ A
B-elim′ W D (Uᵣ′ l′ l< ⊢Γ) =
  ⊥-elim (U≢B W (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ℕᵣ D′) =
  ⊥-elim (ℕ≢B W (whrDet* (red D′ , ℕₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Emptyᵣ D′) =
  ⊥-elim (Empty≢B W (whrDet* (red D′ , Emptyₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Unitᵣ D′) =
  ⊥-elim (Unit≢B W (whrDet* (red D′ , Unitₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ne′ K D′ neK K≡K) =
  ⊥-elim (B≢ne W neK (whrDet* (D , ⟦ W ⟧ₙ) (red D′ , ne neK)))
B-elim′ BΠ D (Bᵣ′ BΣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) with whrDet* (D , Πₙ) (red D′ , Σₙ)
... | ()
B-elim′ BΣ D (Bᵣ′ BΠ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) with whrDet* (D , Σₙ) (red D′ , Πₙ)
... | ()
B-elim′ BΠ D (Bᵣ′ BΠ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Bᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
B-elim′ BΣ D (Bᵣ′ BΣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Bᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
B-elim′ W D (emb 0<1 x) with B-elim′ W D x
B-elim′ W D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
B-elim′ W D (emb 0<1 x) | emb () x₂

B-elim : ∀ {F G l} W → Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G
B-elim W [Π] = B-elim′ W (id (escape [Π])) [Π]

Π-elim : ∀ {F G l} → Γ ⊩⟨ l ⟩ Π F ▹ G → Γ ⊩⟨ l ⟩B⟨ BΠ ⟩ Π F ▹ G
Π-elim [Π] = B-elim′ BΠ (id (escape [Π])) [Π]

Σ-elim : ∀ {F G l} → Γ ⊩⟨ l ⟩ Σ F ▹ G → Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G
Σ-elim [Σ] = B-elim′ BΣ (id (escape [Σ])) [Σ]

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

-- A view for constructor equality of types where embeddings are ignored
data ShapeView (Γ : Con Term n) : ∀ l l′ A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ B) → Set where
  Uᵥ : ∀ {l l′} UA UB → ShapeView Γ l l′ U U (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  Unitᵥ : ∀ {A B l l′} UnitA UnitB → ShapeView Γ l l′ A B (Unitᵣ UnitA) (Unitᵣ UnitB)
  ne  : ∀ {A B l l′} neA neB
      → ShapeView Γ l l′ A B (ne neA) (ne neB)
  Bᵥ : ∀ {A B l l′} W BA BB
    → ShapeView Γ l l′ A B (Bᵣ W BA) (Bᵣ W BB)
  emb⁰¹ : ∀ {A B l p q}
        → ShapeView Γ ⁰ l A B p q
        → ShapeView Γ ¹ l A B (emb 0<1 p) q
  emb¹⁰ : ∀ {A B l p q}
        → ShapeView Γ l ⁰ A B p q
        → ShapeView Γ l ¹ A B p (emb 0<1 q)

-- Construct an shape view from an equality (aptly named)
goodCases : ∀ {l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → ShapeView Γ l l′ A B [A] [B]
-- Diagonal cases
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Unitᵣ UnitA) (Unitᵣ UnitB) A≡B = Unitᵥ UnitA UnitB
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (Bᵣ BΠ ΠA) (Bᵣ BΠ ΠB) A≡B = Bᵥ BΠ ΠA ΠB
goodCases (Bᵣ BΣ ΣA) (Bᵣ BΣ ΣB) A≡B = Bᵥ BΣ ΣA ΣB
--goodCases (Σᵣ ΣA) (Σᵣ ΣB) A≡B = Σᵥ ΣA ΣB

goodCases {l = l} [A] (emb 0<1 x) A≡B =
  emb¹⁰ (goodCases {l = l} {⁰} [A] x A≡B)
goodCases {l′ = l} (emb 0<1 x) [B] A≡B =
  emb⁰¹ (goodCases {l = ⁰} {l} x [B] A≡B)

-- Refutable cases
-- U ≡ _
goodCases (Uᵣ′ _ _ ⊢Γ) (ℕᵣ D) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (Emptyᵣ D) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (Unitᵣ D) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (ne′ K D neK K≡K) PE.refl =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ ⊢Γ) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))

-- ℕ ≡ _
goodCases (ℕᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (ℕᵣ _) (Emptyᵣ D') D with whrDet* (D , ℕₙ) (red D' , Emptyₙ)
... | ()
goodCases (ℕᵣ x) (Unitᵣ D') D with whrDet* (D , ℕₙ) (red D' , Unitₙ)
... | ()
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢B W (whrDet* (A≡B , ℕₙ) (red D₁ , ⟦ W ⟧ₙ)))

-- Empty ≢ _
goodCases (Emptyᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (Emptyᵣ _) (Unitᵣ D') D with whrDet* (red D' , Unitₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢B W (whrDet* (A≡B , Emptyₙ) (red D₁ , ⟦ W ⟧ₙ)))

-- Unit ≡ _
goodCases (Unitᵣ _) (Uᵣ x₁) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (Unitᵣ _) (Emptyᵣ D') D with whrDet* (red D' , Emptyₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Unit≢ne neK (whrDet* (A≡B , Unitₙ) (red D₁ , ne neK)))
goodCases (Unitᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Unit≢B W (whrDet* (A≡B , Unitₙ) (red D₁ , ⟦ W ⟧ₙ)))

-- ne ≡ _
goodCases (ne′ K D neK K≡K) (Uᵣ ⊢Γ) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Unitᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Unit≢ne neM (whrDet* (red D₁ , Unitₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (B≢ne W neM (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D′ , ne neM)))

-- Π ≡ _
goodCases (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whnfRed* D′ Uₙ
... | ()
goodCases (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)
... | ()
goodCases (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)
... | ()
goodCases (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Unitₙ) (D′ , Πₙ)
... | ()
goodCases (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
  (B₌ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′]) with whrDet* (red D′ , Σₙ) (D′₁ , Πₙ)
... | ()
goodCases (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (B≢ne BΠ neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))

-- Σ ≡ _
goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whnfRed* D′ Uₙ
... | ()
goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , ℕₙ) (D′ , Σₙ)
... | ()
goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Emptyₙ) (D′ , Σₙ)
... | ()
goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Unitₙ) (D′ , Σₙ)
... | ()
goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΠ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
  (B₌ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′]) with whrDet* (red D′ , Πₙ) (D′₁ , Σₙ)
... | ()
goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (B≢ne BΣ neK (whrDet* (D′ , Σₙ) (red D₁ , ne neK)))

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A′] : Γ ⊩⟨ l′ ⟩ A)
              → ShapeView Γ l l′ A A [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ (Γ : Con Term n) : ∀ l l′ l″ A B C
                 (p : Γ ⊩⟨ l   ⟩ A)
                 (q : Γ ⊩⟨ l′  ⟩ B)
                 (r : Γ ⊩⟨ l″ ⟩ C) → Set where
  Uᵥ : ∀ {l l′ l″} UA UB UC → ShapeView₃ Γ l l′ l″ U U U (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C l l′ l″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  Unitᵥ : ∀ {A B C l l′ l″} UnitA UnitB UnitC
    → ShapeView₃ Γ l l′ l″ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ UnitC)
  ne  : ∀ {A B C l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C (ne neA) (ne neB) (ne neC)
  Bᵥ : ∀ {A B C l l′ l″} W BA BB BC
    → ShapeView₃ Γ l l′ l″ A B C (Bᵣ W BA) (Bᵣ W BB) (Bᵣ W BC)
  emb⁰¹¹ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ ⁰ l l′ A B C p q r
         → ShapeView₃ Γ ¹ l l′ A B C (emb 0<1 p) q r
  emb¹⁰¹ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ l ⁰ l′ A B C p q r
         → ShapeView₃ Γ l ¹ l′ A B C p (emb 0<1 q) r
  emb¹¹⁰ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ l l′ ⁰ A B C p q r
         → ShapeView₃ Γ l l′ ¹ A B C p q (emb 0<1 r)

-- Combines two two-way views into a three-way view
combine : ∀ {l l′ l″ l‴ A B C [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B [A] [B]
        → ShapeView Γ l″ l‴ B C [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C [A] [B] [C]
-- Diagonal cases
combine (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine (Unitᵥ UnitA₁ UnitB₁) (Unitᵥ UnitA UnitB) = Unitᵥ UnitA₁ UnitB₁ UnitB
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (Bᵥ BΠ ΠA₁ ΠB₁) (Bᵥ BΠ ΠA ΠB) = Bᵥ BΠ ΠA₁ ΠB₁ ΠB
combine (Bᵥ BΣ ΣA₁ ΣB₁) (Bᵥ BΣ ΣA ΣB) = Bᵥ BΣ ΣA₁ ΣB₁ ΣB
combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])

-- Refutable cases
-- U ≡ _
combine (Uᵥ UA UB) (ℕᵥ ℕA ℕB) with whnfRed* (red ℕA) Uₙ
... | ()
combine (Uᵥ UA UB) (Emptyᵥ EmptyA EmptyB) with whnfRed* (red EmptyA) Uₙ
... | ()
combine (Uᵥ UA UB) (Unitᵥ UnA UnB) with whnfRed* (red UnA) Uₙ
... | ()
combine (Uᵥ UA UB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (Uᵥ UA UB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))

-- ℕ ≡ _
combine (ℕᵥ ℕA ℕB) (Uᵥ UA UB) with whnfRed* (red ℕB) Uₙ
... | ()
combine (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Unitᵥ UnA UnB) with whrDet* (red ℕB , ℕₙ) (red UnA , Unitₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine (ℕᵥ ℕA ℕB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕB , ℕₙ) (red D , ⟦ W ⟧ₙ)))

-- Empty ≡ _
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) with whnfRed* (red EmptyB) Uₙ
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Unitᵥ UnA UnB) with whrDet* (red EmptyB , Emptyₙ) (red UnA , Unitₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine (Emptyᵥ EmptyA EmptyB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyB , Emptyₙ) (red D , ⟦ W ⟧ₙ)))

-- Unit ≡ _
combine (Unitᵥ UnitA UnitB) (Uᵥ UA UB) with whnfRed* (red UnitB) Uₙ
... | ()
combine (Unitᵥ UnitA UnitB) (ℕᵥ ℕA ℕB) with whrDet* (red UnitB , Unitₙ) (red ℕA , ℕₙ)
... | ()
combine (Unitᵥ UnitA UnitB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red UnitB , Unitₙ) (red EmptyA , Emptyₙ)
... | ()
combine (Unitᵥ UnitA UnitB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnitB , Unitₙ) (red D , ne neK)))
combine (Unitᵥ UnitA UnitB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (Unit≢B W (whrDet* (red UnitB , Unitₙ) (red D , ⟦ W ⟧ₙ)))

-- ne ≡ _
combine (ne neA (ne K D neK K≡K)) (Uᵥ UA UB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Unitᵥ UnA UnB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnA , Unitₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Bᵥ W (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))

-- Π/Σ ≡ _
combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕA , ℕₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyA , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Unitᵥ UnitA UnitB) =
  ⊥-elim (Unit≢B W (whrDet* (red UnitA , Unitₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W BA (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))
combine (Bᵥ BΠ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΣA)
  with whrDet* (red D , Πₙ) (red D′ , Σₙ)
... | ()
combine (Bᵥ BΣ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΠA)
  with whrDet* (red D , Σₙ) (red D′ , Πₙ)
... | ()
