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

open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE

-- Type for maybe embeddings of reducible types
data MaybeEmb (l : TypeLevel) (⊩⟨_⟩ : TypeLevel → Set) : Set where
  noemb : ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : ∀ {l′} → l′ < l → MaybeEmb l′ ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

-- Specific reducible types with possible embedding

_⊩⟨_⟩U : (Γ : Con Term) (l : TypeLevel) → Set
Γ ⊩⟨ l ⟩U = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U)

_⊩⟨_⟩ℕ_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩Empty_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

_⊩⟨_⟩Unit_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Unit A = MaybeEmb l (λ l′ → Γ ⊩Unit A)

_⊩⟨_⟩ne_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ne A = MaybeEmb l (λ l′ → Γ ⊩ne A)

_⊩⟨_⟩Π_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Π A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Π A)

-- Construct a general reducible type from a specific

U-intr : ∀ {Γ l} → Γ ⊩⟨ l ⟩U → Γ ⊩⟨ l ⟩ U
U-intr (noemb x) = Uᵣ x
U-intr (emb 0<1 x) = emb 0<1 (U-intr x)

ℕ-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb 0<1 x) = emb 0<1 (ℕ-intr x)

Empty-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr (emb 0<1 x) = emb 0<1 (Empty-intr x)

Unit-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩Unit A → Γ ⊩⟨ l ⟩ A
Unit-intr (noemb x) = Unitᵣ x
Unit-intr (emb 0<1 x) = emb 0<1 (Unit-intr x)

ne-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ne A → Γ ⊩⟨ l ⟩ A
ne-intr (noemb x) = ne x
ne-intr (emb 0<1 x) = emb 0<1 (ne-intr x)

Π-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩Π A → Γ ⊩⟨ l ⟩ A
Π-intr (noemb x) = Πᵣ x
Π-intr (emb 0<1 x) = emb 0<1 (Π-intr x)

-- Construct a specific reducible type from a general with some criterion

U-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ U → Γ ⊩⟨ l ⟩U
U-elim (Uᵣ′ l′ l< ⊢Γ) = noemb (Uᵣ l′ l< ⊢Γ)
U-elim (ℕᵣ D) = ⊥-elim (U≢ℕ (whnfRed* (red D) Uₙ))
U-elim (Emptyᵣ D) = ⊥-elim (U≢Empty (whnfRed* (red D) Uₙ))
U-elim (Unitᵣ D) = ⊥-elim (U≢Unit (whnfRed* (red D) Uₙ))
U-elim (ne′ K D neK K≡K) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-elim (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
U-elim (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) with whnfRed* (red D) Uₙ
... | ()
U-elim (emb 0<1 x) with U-elim x
U-elim (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
U-elim (emb 0<1 x) | emb () x₁

ℕ-elim′ : ∀ {A Γ l} → Γ ⊢ A ⇒* ℕ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ l′ l< ⊢Γ) = ⊥-elim (U≢ℕ (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ℕₙ)))
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Πᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢Π (whrDet* (D , ℕₙ) (red D′ , Πₙ)))
ℕ-elim′ D (Σᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) with whrDet* (D , ℕₙ) (red D′ , Σₙ)
... | ()
ℕ-elim′ D (Emptyᵣ D′) =
  ⊥-elim (ℕ≢Empty (whrDet* (D , ℕₙ) (red D′ , Emptyₙ)))
ℕ-elim′ D (Unitᵣ D′) =
  ⊥-elim (ℕ≢Unit (whrDet* (D , ℕₙ) (red D′ , Unitₙ)))
ℕ-elim′ D (emb 0<1 x) with ℕ-elim′ D x
ℕ-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim′ D (emb 0<1 x) | emb () x₂

ℕ-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

Empty-elim′ : ∀ {A Γ l} → Γ ⊢ A ⇒* Empty → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Uᵣ′ l′ l< ⊢Γ) = ⊥-elim (U≢Empty (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Emptyₙ)))
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (Unitᵣ D′) =
  ⊥-elim (Empty≢Unit (whrDet* (D , Emptyₙ) (red D′ , Unitₙ)))
Empty-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Πᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢Π (whrDet* (D , Emptyₙ) (red D′ , Πₙ)))
Empty-elim′ D (Σᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) with whrDet* (D , Emptyₙ) (red D′ , Σₙ)
... | ()
Empty-elim′ D (ℕᵣ D′) =
  ⊥-elim (Empty≢ℕ (whrDet* (D , Emptyₙ) (red D′ , ℕₙ)))
Empty-elim′ D (emb 0<1 x) with Empty-elim′ D x
Empty-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Empty-elim′ D (emb 0<1 x) | emb () x₂

Empty-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ Empty → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

Unit-elim′ : ∀ {A Γ l} → Γ ⊢ A ⇒* Unit → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Unit A
Unit-elim′ D (Uᵣ′ l′ l< ⊢Γ) = ⊥-elim (U≢Unit (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Unitₙ)))
Unit-elim′ D (Unitᵣ D′) = noemb D′
Unit-elim′ D (Emptyᵣ D′) with whrDet* (D , Unitₙ) (red D′ , Emptyₙ)
... | ()
Unit-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (red D′ , ne neK)))
Unit-elim′ D (Πᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Unit≢Π (whrDet* (D , Unitₙ) (red D′ , Πₙ)))
Unit-elim′ D (Σᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) with whrDet* (D , Unitₙ) (red D′ , Σₙ)
... | ()
Unit-elim′ D (ℕᵣ D′) with whrDet* (D , Unitₙ) (red D′ , ℕₙ)
... | ()
Unit-elim′ D (emb 0<1 x) with Unit-elim′ D x
Unit-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Unit-elim′ D (emb 0<1 x) | emb () x₂

Unit-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ Unit → Γ ⊩⟨ l ⟩Unit Unit
Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

ne-elim′ : ∀ {A Γ l K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ne A
ne-elim′ D neK (Uᵣ′ l′ l< ⊢Γ) =
  ⊥-elim (U≢ne neK (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (Unitᵣ D′) = ⊥-elim (nee neK (whrDet* (red D′ , Unitₙ) (D , ne neK)))
  where nee : ∀ {K} → Neutral K → Unit PE.≢ K
        nee () PE.refl
ne-elim′ D neK (ne′ K D′ neK′ K≡K) = noemb (ne K D′ neK′ K≡K)
ne-elim′ D neK (Πᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢ne neK (whrDet* (red D′ , Πₙ) (D , ne neK)))
ne-elim′ D neK (Σᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Σ≢ne neK (whrDet* (red D′ , Σₙ) (D , ne neK)))
ne-elim′ D neK (emb 0<1 x) with ne-elim′ D neK x
ne-elim′ D neK (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ne-elim′ D neK (emb 0<1 x) | emb () x₂

ne-elim : ∀ {Γ l K} → Neutral K  → Γ ⊩⟨ l ⟩ K → Γ ⊩⟨ l ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

Π-elim′ : ∀ {A Γ F G l} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Π A
Π-elim′ D (Uᵣ′ l′ l< ⊢Γ) = ⊥-elim (U≢Π (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Πₙ)))
Π-elim′ D (ℕᵣ D′) = ⊥-elim (ℕ≢Π (whrDet* (red D′ , ℕₙ) (D , Πₙ)))
Π-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢Π (whrDet* (red D′ , Emptyₙ) (D , Πₙ)))
Π-elim′ D (Unitᵣ D′) = ⊥-elim (Unit≢Π (whrDet* (red D′ , Unitₙ) (D , Πₙ)))
Π-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Π≢ne neK (whrDet* (D , Πₙ) (red D′ , ne neK)))
Π-elim′ D (Πᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Bᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
Π-elim′ D (Σᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) with whrDet* (red D′ , Σₙ) (D , Πₙ)
... | ()
Π-elim′ D (emb 0<1 x) with Π-elim′ D x
Π-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Π-elim′ D (emb 0<1 x) | emb () x₂

Π-elim : ∀ {Γ F G l} → Γ ⊩⟨ l ⟩ Π F ▹ G → Γ ⊩⟨ l ⟩Π Π F ▹ G
Π-elim [Π] = Π-elim′ (id (escape [Π])) [Π]

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

-- A view for constructor equality of types where embeddings are ignored
data ShapeView Γ : ∀ l l′ A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ B) → Set where
  Uᵥ : ∀ {l l′} UA UB → ShapeView Γ l l′ U U (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  Unitᵥ : ∀ {A B l l′} UnitA UnitB → ShapeView Γ l l′ A B (Unitᵣ UnitA) (Unitᵣ UnitB)
  ne  : ∀ {A B l l′} neA neB
      → ShapeView Γ l l′ A B (ne neA) (ne neB)
  Πᵥ : ∀ {A B l l′} ΠA ΠB
    → ShapeView Γ l l′ A B (Πᵣ ΠA) (Πᵣ ΠB)
  Σᵥ : ∀ {A B l l′} ΣA ΣB
    → ShapeView Γ l l′ A B (Σᵣ ΣA) (Σᵣ ΣB)
  emb⁰¹ : ∀ {A B l p q}
        → ShapeView Γ ⁰ l A B p q
        → ShapeView Γ ¹ l A B (emb 0<1 p) q
  emb¹⁰ : ∀ {A B l p q}
        → ShapeView Γ l ⁰ A B p q
        → ShapeView Γ l ¹ A B p (emb 0<1 q)

-- Construct an shape view from an equality (aptly named)
goodCases : ∀ {l l′ Γ A B} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → ShapeView Γ l l′ A B [A] [B]
-- Diagonal cases
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Unitᵣ UnitA) (Unitᵣ UnitB) A≡B = Unitᵥ UnitA UnitB
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (Πᵣ ΠA) (Πᵣ ΠB) A≡B = Πᵥ ΠA ΠB
goodCases (Σᵣ ΣA) (Σᵣ ΣB) A≡B = Σᵥ ΣA ΣB

goodCases {l} [A] (emb 0<1 x) A≡B =
  emb¹⁰ (goodCases {l} {⁰} [A] x A≡B)
goodCases {l′ = l} (emb 0<1 x) [B] A≡B =
  emb⁰¹ (goodCases {⁰} {l} x [B] A≡B)

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
goodCases (Uᵣ′ _ _ ⊢Γ) (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl with whnfRed* (red D) Uₙ
... | ()

-- ℕ ≡ _
goodCases (ℕᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (ℕᵣ _) (Emptyᵣ D') D with whrDet* (D , ℕₙ) (red D' , Emptyₙ)
... | ()
goodCases (ℕᵣ x) (Unitᵣ D') D with whrDet* (D , ℕₙ) (red D' , Unitₙ)
... | ()
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Πᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B with whrDet* (A≡B , ℕₙ) (red D₁ , Πₙ)
... | ()
goodCases (ℕᵣ D) (Σᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B with whrDet* (A≡B , ℕₙ) (red D₁ , Σₙ)
... | ()

-- Empty ≢ _
goodCases (Emptyᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (Emptyᵣ _) (Unitᵣ D') D with whrDet* (red D' , Unitₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ D) (Πᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B with whrDet* (A≡B , Emptyₙ) (red D₁ , Πₙ)
... | ()
goodCases (Emptyᵣ D) (Σᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B with whrDet* (A≡B , Emptyₙ) (red D₁ , Σₙ)
... | ()

-- ne ≡ _
goodCases (ne′ K D neK K≡K) (Uᵣ ⊢Γ) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Unitᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Unit≢ne neM (whrDet* (red D₁ , Unitₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Πᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Π≢ne neM (whrDet* (red D₁ , Πₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Σᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Σ≢ne neM (whrDet* (red D₁ , Σₙ) (red D′ , ne neM)))

-- Π ≡ _
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whnfRed* D′ Uₙ
... | ()
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)
... | ()
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)
... | ()
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Unitₙ) (D′ , Πₙ)
... | ()
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Σᵣ′ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
  (B₌ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′]) with whrDet* (red D′ , Σₙ) (D′₁ , Πₙ)
... | ()
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢ne neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))

-- Σ ≡ _
goodCases (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whnfRed* D′ Uₙ
... | ()
goodCases (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , ℕₙ) (D′ , Σₙ)
... | ()
goodCases (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Emptyₙ) (D′ , Σₙ)
... | ()
goodCases (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Unitₙ) (D′ , Σₙ)
... | ()
goodCases (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πᵣ′ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
  (B₌ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′]) with whrDet* (red D′ , Πₙ) (D′₁ , Σₙ)
... | ()
goodCases (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Σ≢ne neK (whrDet* (D′ , Σₙ) (red D₁ , ne neK)))

-- Unit ≡ _
goodCases (Unitᵣ _) (Uᵣ x₁) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (Unitᵣ _) (Emptyᵣ D') D with whrDet* (red D' , Emptyₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Unit≢ne neK (whrDet* (A≡B , Unitₙ) (red D₁ , ne neK)))
goodCases (Unitᵣ D) (Πᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B with whrDet* (A≡B , Unitₙ) (red D₁ , Πₙ)
... | ()
goodCases (Unitᵣ D) (Σᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B with whrDet* (A≡B , Unitₙ) (red D₁ , Σₙ)
... | ()

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ Γ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A′] : Γ ⊩⟨ l′ ⟩ A)
              → ShapeView Γ l l′ A A [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ Γ : ∀ l l′ l″ A B C
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
  Πᵥ : ∀ {A B C l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C (Πᵣ ΠA) (Πᵣ ΠB) (Πᵣ ΠC)
  Σᵥ : ∀ {A B C l l′ l″} ΣA ΣB ΣC
    → ShapeView₃ Γ l l′ l″ A B C (Σᵣ ΣA) (Σᵣ ΣB) (Σᵣ ΣC)
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
combine : ∀ {Γ l l′ l″ l‴ A B C [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B [A] [B]
        → ShapeView Γ l″ l‴ B C [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C [A] [B] [C]
-- Diagonal cases
combine (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine (Unitᵥ UnitA₁ UnitB₁) (Unitᵥ UnitA UnitB) = Unitᵥ UnitA₁ UnitB₁ UnitB
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (Πᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = Πᵥ ΠA₁ ΠB₁ ΠB
combine (Σᵥ ΣA₁ ΣB₁) (Σᵥ ΣA ΣB) = Σᵥ ΣA₁ ΣB₁ ΣB
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
combine (Uᵥ UA UB) (Πᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) with whnfRed* (red D) Uₙ
... | ()
combine (Uᵥ UA UB) (Σᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΣB) with whnfRed* (red D) Uₙ
... | ()

-- ℕ ≡ _
combine (ℕᵥ ℕA ℕB) (Uᵥ UA UB) = ⊥-elim (U≢ℕ (whnfRed* (red ℕB) Uₙ))
combine (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (ℕ≢Empty (whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)))
combine (ℕᵥ ℕA ℕB) (Unitᵥ UnA UnB) with whrDet* (red ℕB , ℕₙ) (red UnA , Unitₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine (ℕᵥ ℕA ℕB) (Πᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine (ℕᵥ ℕA ℕB) (Σᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΣB) with whrDet* (red ℕB , ℕₙ) (red D , Σₙ)
... | ()

-- Empty ≡ _
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) =
  ⊥-elim (U≢Empty (whnfRed* (red EmptyB) Uₙ))
combine (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) =
  ⊥-elim (Empty≢ℕ (whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)))
combine (Emptyᵥ EmptyA EmptyB) (Unitᵥ UnA UnB) with whrDet* (red EmptyB , Emptyₙ) (red UnA , Unitₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine (Emptyᵥ EmptyA EmptyB) (Πᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) with whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Σᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) with whrDet* (red EmptyB , Emptyₙ) (red D , Σₙ)
... | ()

-- ne ≡ _
combine (ne neA (ne K D neK K≡K)) (Uᵥ UA UB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Unitᵥ UnA UnB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnA , Unitₙ) (red D , ne neK)))
combine (ne neA (ne K D₁ neK K≡K)) (Πᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine (ne neA (ne K D₁ neK K≡K)) (Σᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Σ≢ne neK (whrDet* (red D , Σₙ) (red D₁ , ne neK)))

-- Π ≡ _
combine (Πᵥ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
combine (Πᵥ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine (Πᵥ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine (Πᵥ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Unitᵥ UnitA UnitB) with whrDet* (red UnitA , Unitₙ) (red D , Πₙ)
... | ()
combine (Πᵥ ΠA (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine (Πᵥ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Σᵥ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΣA)
  with whrDet* (red D , Πₙ) (red D′ , Σₙ)
... | ()

-- Σ ≡ _
combine (Σᵥ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) with whnfRed* (red D) Uₙ
... | ()
combine (Σᵥ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) with whrDet* (red ℕA , ℕₙ) (red D , Σₙ)
... | ()
combine (Σᵥ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) with whrDet* (red EmptyA , Emptyₙ) (red D , Σₙ)
... | ()
combine (Σᵥ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Unitᵥ UnitA UnitB) with whrDet* (red UnitA , Unitₙ) (red D , Σₙ)
... | ()
combine (Σᵥ ΣA (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Σ≢ne neK (whrDet* (red D₁ , Σₙ) (red D , ne neK)))
combine (Σᵥ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Πᵥ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΠA)
  with whrDet* (red D , Σₙ) (red D′ , Πₙ)
... | ()

-- Unit ≡ _
combine (Unitᵥ UnitA UnitB) (Uᵥ UA UB) with whnfRed* (red UnitB) Uₙ
... | ()
combine (Unitᵥ UnitA UnitB) (ℕᵥ ℕA ℕB) with whrDet* (red UnitB , Unitₙ) (red ℕA , ℕₙ)
... | ()
combine (Unitᵥ UnitA UnitB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red UnitB , Unitₙ) (red EmptyA , Emptyₙ)
... | ()
combine (Unitᵥ UnitA UnitB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnitB , Unitₙ) (red D , ne neK)))
combine (Unitᵥ UnitA UnitB) (Πᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) with whrDet* (red UnitB , Unitₙ) (red D , Πₙ)
... | ()
combine (Unitᵥ UnitA UnitB) (Σᵥ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) with whrDet* (red UnitB , Unitₙ) (red D , Σₙ)
... | ()
