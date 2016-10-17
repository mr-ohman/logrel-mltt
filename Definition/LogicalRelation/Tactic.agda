module Definition.LogicalRelation.Tactic where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE
open import Relation.Nullary


U-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ U → ⊢ Γ
U-elim (U ⊢Γ) = ⊢Γ
U-elim (ℕ D) = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
U-elim (ne D neK) = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
U-elim (Π D ⊢F ⊢G [F] [G] G-ext) = ⊥-elim (U≢Π (whnfRed*' (red D) U))
U-elim (emb {l< = 0<1} x) = U-elim x

ℕ-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊢ ℕ :⇒*: ℕ
ℕ-elim (ℕ D) = D
ℕ-elim (ne D neK) = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
ℕ-elim (Π D ⊢F ⊢G [F] [G] G-ext) = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
ℕ-elim (emb {l< = 0<1} x) = ℕ-elim x

ne-elim : ∀ {Γ l K} → Γ ⊩⟨ l ⟩ K → Neutral K
        → ∃ λ K' → Γ ⊢ K :⇒*: K' × Neutral K'
ne-elim (U ⊢Γ) ()
ne-elim (ℕ D) neK = ⊥-elim (ℕ≢ne neK (PE.sym (whnfRed*' (red D) (ne neK))))
ne-elim (ne D neK₁) neK = _ , D , neK₁
ne-elim (Π D ⊢F ⊢G [F] [G] G-ext) neK =
  ⊥-elim (Π≢ne neK (PE.sym (whnfRed*' (red D) (ne neK))))
ne-elim (emb {l< = 0<1} x) neK = ne-elim x neK

Π-elim : ∀ {Γ F G l} → Γ ⊩⟨ l ⟩ Π F ▹ G
       → ∃ λ l'
       → Γ ⊢ F × (Γ ∙ F) ⊢ G
       × ∃ λ ([F] : wk-prop l' Γ F)
       → ∃ λ ([G] : wk-subst-prop l' Γ F G [F])
       → wk-substEq-prop l' Γ F G [F] [G]
Π-elim (ℕ D) = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
Π-elim (ne D neK) = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
Π-elim (Π D ⊢F ⊢G [F] [G] G-ext) with Π-PE-injectivity (whnfRed*' (red D) Π)
... | F≡F' , G≡G' rewrite F≡F' | G≡G' = _ , ⊢F , ⊢G , [F] , [G] , G-ext
Π-elim (emb {l< = 0<1} x) = Π-elim x

data Tactic Γ : ∀ l l' A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ B) → Set where
  ℕ : ∀ {A B l l'} D D₁ → Tactic Γ l l' A B (ℕ D) (ℕ D₁)
  ne  : ∀ {A B K K₁ l l'}
          (D : Γ ⊢ A :⇒*: K)   (neK : Neutral K)
          (D₁ : Γ ⊢ B :⇒*: K₁) (neK₁ : Neutral K₁)
      → Tactic Γ l l' A B (ne D neK) (ne D₁ neK₁)
  Π : ∀ {A B F G F₁ G₁ l l'}
        (D : Γ ⊢ A :⇒*: Π F ▹ G) (⊢F : Γ ⊢ F) (⊢G : Γ ∙ F ⊢ G)
        ([F] : wk-prop l Γ F) ([G] : wk-subst-prop l Γ F G [F])
        (G-ext : wk-substEq-prop l Γ F G [F] [G])
        (D₁ : Γ ⊢ B :⇒*: Π F₁ ▹ G₁) (⊢F₁ : Γ ⊢ F₁) (⊢G₁ : Γ ∙ F₁ ⊢ G₁)
        ([F]₁ : wk-prop l' Γ F₁)  ([G]₁ : wk-subst-prop l' Γ F₁ G₁ [F]₁)
        (G-ext₁ : wk-substEq-prop l' Γ F₁ G₁ [F]₁ [G]₁)
    → Tactic Γ l l' A B (Π D ⊢F ⊢G [F] [G] G-ext)
                        (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
  U : (⊢Γ ⊢Γ₁ : ⊢ Γ) → Tactic Γ ¹ ¹ U U (U {l< = 0<1} ⊢Γ) (U {l< = 0<1} ⊢Γ₁)
  emb⁰¹ : ∀ {A B l p q}
        → Tactic Γ ⁰ l A B p q
        → Tactic Γ ¹ l A B (emb {l< = 0<1} p) q
  emb¹⁰ : ∀ {A B l p q}
        → Tactic Γ l ⁰ A B p q
        → Tactic Γ l ¹ A B p (emb {l< = 0<1} q)

goodCases : ∀ {l l' Γ A B} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Tactic Γ l l' A B [A] [B]
goodCases (U {l< = 0<1} ⊢Γ) (U {l< = 0<1} ⊢Γ₁) A≡B = U ⊢Γ ⊢Γ₁
goodCases (U ⊢Γ) (ℕ D) PE.refl = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
goodCases (U ⊢Γ) (ne D neK) PE.refl = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
goodCases (U ⊢Γ) (Π D ⊢F ⊢G [F] [G] G-ext) PE.refl =
  ⊥-elim (U≢Π (whnfRed*' (red D) U))
goodCases (ℕ D) (U ⊢Γ) A≡B = ⊥-elim (U≢ℕ (whnfRed*' A≡B U))
goodCases (ℕ D) (ℕ D₁) A≡B = ℕ D D₁
goodCases (ℕ D) (ne D₁ neK) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet*' (A≡B , ℕ) (red D₁ , ne neK)))
goodCases (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢Π (whrDet*' (A≡B , ℕ) (red D₁ , Π)))
goodCases (ne D neK) (U ⊢Γ) ne[ M , D' , neM , K≡M ] =
  ⊥-elim (U≢ne neM (whnfRed*' (red D') U))
goodCases (ne D neK) (ℕ D₁) ne[ M , D' , neM , K≡M ] =
  ⊥-elim (ℕ≢ne neM (whrDet*' (red D₁ , ℕ) (red D' , ne neM)))
goodCases (ne D neK) (ne D₁ neK₁) A≡B = ne D neK D₁ neK₁
goodCases (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) ne[ M , D' , neM , K≡M ] =
  ⊥-elim (Π≢ne neM (whrDet*' (red D₁ , Π) (red D' , ne neM)))
goodCases (Π D ⊢F ⊢G [F] [G] G-ext) (U ⊢Γ)
          Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (U≢Π (whnfRed*' D' U))
goodCases (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁)
          Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (D' , Π)))
goodCases (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK)
          Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (Π≢ne neK (whrDet*' (D' , Π) (red D₁ , ne neK)))
goodCases (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) A≡B =
  Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
goodCases {l} [A] (emb {l< = 0<1} x) A≡B =
  emb¹⁰ (goodCases {l} {⁰} [A] x A≡B)
goodCases {l' = l} (emb {l< = 0<1} x) [B] A≡B =
  emb⁰¹ (goodCases {⁰} {l} x [B] A≡B)

goodCasesRefl : ∀ {l l' Γ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A'] : Γ ⊩⟨ l' ⟩ A)
              → Tactic Γ l l' A A [A] [A']
goodCasesRefl [A] [A'] = goodCases [A] [A'] (reflEq [A])
