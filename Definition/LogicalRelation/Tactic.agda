module Definition.LogicalRelation.Tactic where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Soundness

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE
open import Relation.Nullary


data MaybeEmb : TypeLevel → (TypeLevel → Set) → Set where
  noemb : ∀ {l ⊩⟨_⟩} → ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : ∀ {l l' ⊩⟨_⟩} → l' < l → MaybeEmb l' ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

_⊩⟨_⟩U : (Γ : Con Term) (l : TypeLevel) → Set
Γ ⊩⟨ l ⟩U = MaybeEmb l (λ l' → Γ ⊩'⟨ l' ⟩U)

_⊩⟨_⟩ℕ_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l' → Γ ⊩'⟨ l' ⟩ℕ A)

_⊩⟨_⟩ne_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ne A = MaybeEmb l (λ l' → Γ ⊩'⟨ l' ⟩ne A)

_⊩⟨_⟩Π_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Π A = MaybeEmb l (λ l' → Γ ⊩'⟨ l' ⟩Π A)

U-intr : ∀ {Γ l} → Γ ⊩⟨ l ⟩U → Γ ⊩⟨ l ⟩ U
U-intr (noemb x) = U x
U-intr (emb 0<1 x) = emb {l< = 0<1} (U-intr x)

ℕ-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A
ℕ-intr (noemb x) = ℕ x
ℕ-intr (emb 0<1 x) = emb {l< = 0<1} (ℕ-intr x)

ne-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ne A → Γ ⊩⟨ l ⟩ A
ne-intr (noemb x) = ne x
ne-intr (emb 0<1 x) = emb {l< = 0<1} (ne-intr x)

Π-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩Π A → Γ ⊩⟨ l ⟩ A
Π-intr (noemb x) = Π x
Π-intr (emb 0<1 x) = emb {l< = 0<1} (Π-intr x)

U-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ U → Γ ⊩⟨ l ⟩U
U-elim (U (U l' l< ⊢Γ)) = noemb (U l' l< ⊢Γ)
U-elim (ℕ (ℕ D)) = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
U-elim (ne (ne K D neK)) = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
U-elim (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) = ⊥-elim (U≢Π (whnfRed*' (red D) U))
U-elim (emb {l< = 0<1} x) with U-elim x
U-elim (emb {l< = 0<1} x) | noemb x₁ = emb 0<1 (noemb x₁)
U-elim (emb {l< = 0<1} x) | emb () x₁

ℕ-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim (ℕ (ℕ D)) = noemb (ℕ D)
ℕ-elim (ne (ne K D neK)) = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
ℕ-elim (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
ℕ-elim (emb {l< = 0<1} x) with ℕ-elim x
ℕ-elim (emb {l< = 0<1} x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim (emb {l< = 0<1} x) | emb () x₂

ne-elim : ∀ {Γ l K} → Γ ⊩⟨ l ⟩ K → Neutral K → Γ ⊩⟨ l ⟩ne K
ne-elim (U (U l' l< ⊢Γ)) ()
ne-elim (ℕ (ℕ D)) neK = ⊥-elim (ℕ≢ne neK (PE.sym (whnfRed*' (red D) (ne neK))))
ne-elim {l = l} (ne (ne K D neK)) neK₁ = noemb (ne K D neK)
ne-elim (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) neK =
  ⊥-elim (Π≢ne neK (PE.sym (whnfRed*' (red D) (ne neK))))
ne-elim (emb {l< = 0<1} x) neK with ne-elim x neK
ne-elim (emb {l< = 0<1} x) neK | noemb x₁ = emb 0<1 (noemb x₁)
ne-elim (emb {l< = 0<1} x) neK | emb () x₂

Π-elim : ∀ {Γ F G l} → Γ ⊩⟨ l ⟩ Π F ▹ G → Γ ⊩⟨ l ⟩Π Π F ▹ G
Π-elim (ℕ (ℕ D)) = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
Π-elim (ne (ne K D neK)) = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
Π-elim {l = l} (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) =
  noemb (Π F G D ⊢F ⊢G [F] [G] G-ext)
Π-elim (emb {l< = 0<1} x) with Π-elim x
Π-elim (emb {l< = 0<1} x) | noemb x₁ = emb 0<1 (noemb x₁)
Π-elim (emb {l< = 0<1} x) | emb () x₂

extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l' → ⊩⟨ l' ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

data Tactic Γ : ∀ l l' A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ B) → Set where
  U : ∀ {l l'} UA UB → Tactic Γ l l' U U (U UA) (U UB)
  ℕ : ∀ {A B l l'} ℕA ℕB → Tactic Γ l l' A B (ℕ ℕA) (ℕ ℕB)
  ne  : ∀ {A B l l'} neA neB
      → Tactic Γ l l' A B (ne neA) (ne neB)
  Π : ∀ {A B l l'} ΠA ΠB
    → Tactic Γ l l' A B (Π ΠA) (Π ΠB)
  emb⁰¹ : ∀ {A B l p q}
        → Tactic Γ ⁰ l A B p q
        → Tactic Γ ¹ l A B (emb {l< = 0<1} p) q
  emb¹⁰ : ∀ {A B l p q}
        → Tactic Γ l ⁰ A B p q
        → Tactic Γ l ¹ A B p (emb {l< = 0<1} q)

goodCases : ∀ {l l' Γ A B} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Tactic Γ l l' A B [A] [B]
goodCases (U UA) (U UB) A≡B = U UA UB
goodCases (U ⊢Γ) (ℕ (ℕ D)) PE.refl = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
goodCases (U ⊢Γ) (ne (ne K D neK)) PE.refl = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
goodCases (U ⊢Γ) (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) PE.refl =
  ⊥-elim (U≢Π (whnfRed*' (red D) U))
goodCases (ℕ (ℕ D)) (U ⊢Γ) A≡B = ⊥-elim (U≢ℕ (whnfRed*' A≡B U))
goodCases (ℕ ℕA) (ℕ ℕB) A≡B = ℕ ℕA ℕB
goodCases (ℕ (ℕ D)) (ne (ne K D₁ neK)) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet*' (A≡B , ℕ) (red D₁ , ne neK)))
goodCases (ℕ (ℕ D)) (Π (Π F G D₁ ⊢F ⊢G [F] [G] G-ext)) A≡B =
  ⊥-elim (ℕ≢Π (whrDet*' (A≡B , ℕ) (red D₁ , Π)))
goodCases (ne (ne K D neK)) (U ⊢Γ) ne[ M , D' , neM , K≡M ] =
  ⊥-elim (U≢ne neM (whnfRed*' (red D') U))
goodCases (ne (ne K D neK)) (ℕ (ℕ D₁)) ne[ M , D' , neM , K≡M ] =
  ⊥-elim (ℕ≢ne neM (whrDet*' (red D₁ , ℕ) (red D' , ne neM)))
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (ne (ne K D neK)) (Π (Π F G D₁ ⊢F ⊢G [F] [G] G-ext)) ne[ M , D' , neM , K≡M ] =
  ⊥-elim (Π≢ne neM (whrDet*' (red D₁ , Π) (red D' , ne neM)))
goodCases (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (U ⊢Γ)
          Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (U≢Π (whnfRed*' D' U))
goodCases (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (ℕ (ℕ D₁))
          Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (D' , Π)))
goodCases (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (ne (ne K D₁ neK))
          Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (Π≢ne neK (whrDet*' (D' , Π) (red D₁ , ne neK)))
goodCases (Π ΠA) (Π ΠB) A≡B = Π ΠA ΠB
goodCases {l} [A] (emb {l< = 0<1} x) A≡B =
  emb¹⁰ (goodCases {l} {⁰} [A] x A≡B)
goodCases {l' = l} (emb {l< = 0<1} x) [B] A≡B =
  emb⁰¹ (goodCases {⁰} {l} x [B] A≡B)

goodCasesRefl : ∀ {l l' Γ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A'] : Γ ⊩⟨ l' ⟩ A)
              → Tactic Γ l l' A A [A] [A']
goodCasesRefl [A] [A'] = goodCases [A] [A'] (reflEq [A])
