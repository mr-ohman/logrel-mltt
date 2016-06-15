module Definition.LogicalRelation.Tactic where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Reflexivity

open import Tools.Context

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE
open import Relation.Nullary

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
    → Tactic Γ l l' A B (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
  U : (⊢Γ ⊢Γ₁ : ⊢ Γ) → Tactic Γ ¹ ¹ U U (U {l< = 0<1} ⊢Γ) (U {l< = 0<1} ⊢Γ₁)
  emb⁰¹ : ∀ {A B l p q} → Tactic Γ ⁰ l A B p q → Tactic Γ ¹ l A B (emb {l< = 0<1} p) q
  emb¹⁰ : ∀ {A B l p q} → Tactic Γ l ⁰ A B p q → Tactic Γ l ¹ A B p (emb {l< = 0<1} q)

goodCases : ∀ {l l' Γ A B} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Tactic Γ l l' A B [A] [B]
goodCases {⁰} {l} (U {l< = ()} ⊢Γ) (U ⊢Γ₁) A≡B
goodCases {l} {⁰} (U ⊢Γ) (U {l< = ()} ⊢Γ₁) A≡B
goodCases {¹} {¹} (U {l< = 0<1} ⊢Γ) (U {l< = 0<1} ⊢Γ₁) A≡B = U ⊢Γ ⊢Γ₁
goodCases (U ⊢Γ) (ℕ D) PE.refl = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
goodCases (U ⊢Γ) (ne D neK) PE.refl = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
goodCases (U ⊢Γ) (Π D ⊢F ⊢G [F] [G] G-ext) PE.refl = ⊥-elim (U≢Π (whnfRed*' (red D) U))
goodCases (ℕ D) (U ⊢Γ) A≡B = ⊥-elim (U≢ℕ (whnfRed*' A≡B U))
goodCases (ℕ D) (ℕ D₁) A≡B = ℕ D D₁
goodCases (ℕ D) (ne D₁ neK) A≡B = ⊥-elim (ℕ≢ne neK (whrDet*' (A≡B , ℕ) (red D₁ , ne neK)))
goodCases (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) A≡B = ⊥-elim (ℕ≢Π (whrDet*' (A≡B , ℕ) (red D₁ , Π)))
goodCases (ne D neK) (U ⊢Γ) ne[ M , D' , neM , K≡M ] = ⊥-elim (U≢ne neM (whnfRed*' (red D') U))
goodCases (ne D neK) (ℕ D₁) ne[ M , D' , neM , K≡M ] = ⊥-elim (ℕ≢ne neM (whrDet*' (red D₁ , ℕ) (red D' , ne neM)))
goodCases (ne D neK) (ne D₁ neK₁) A≡B = ne D neK D₁ neK₁
goodCases (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) ne[ M , D' , neM , K≡M ] = ⊥-elim (Π≢ne neM (whrDet*' (red D₁ , Π) (red D' , ne neM)))
goodCases (Π D ⊢F ⊢G [F] [G] G-ext) (U ⊢Γ) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = ⊥-elim (U≢Π (whnfRed*' D' U))
goodCases (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (D' , Π)))
goodCases (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = ⊥-elim (Π≢ne neK (whrDet*' (D' , Π) (red D₁ , ne neK)))
goodCases (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) A≡B = Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
goodCases {l} {⁰} [A] (emb {l< = ()} x) A≡B
goodCases {l} {¹} [A] (emb {l< = 0<1} x) A≡B = emb¹⁰ (goodCases {l} {⁰} [A] x A≡B)
goodCases {⁰} {l} (emb {l< = ()} x) [B] A≡B
goodCases {¹} {l} (emb {l< = 0<1} x) [B] A≡B = emb⁰¹ (goodCases {⁰} {l} x [B] A≡B)

goodCasesRefl : ∀ {l l' Γ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A'] : Γ ⊩⟨ l' ⟩ A) → Tactic Γ l l' A A [A] [A']
goodCasesRefl [A] [A'] = goodCases [A] [A'] (reflEq [A])

----------------------------------------------------------

--_⊩⟨_,_⟩_[_≡_]
-- data Tactic Γ : ∀ A l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A) → Set where
--   ℕ⁰⁰ : ∀ {A} D D₁ → Tactic Γ A ⁰ ⁰ (ℕ D)  (ℕ D₁)
--   ℕ⁰¹ : ∀ D ⊢Γ₁    → Tactic Γ ℕ ⁰ ¹ (ℕ D)  (ℕ ⊢Γ₁)
--   ℕ¹⁰ : ∀ ⊢Γ D₁    → Tactic Γ ℕ ¹ ⁰ (ℕ ⊢Γ) (ℕ D₁)
--   ℕ¹¹ : ∀ ⊢Γ ⊢Γ₁   → Tactic Γ ℕ ¹ ¹ (ℕ ⊢Γ) (ℕ ⊢Γ₁)
--   ne  : ∀ {A K K₁}
--           (D : Γ ⊢ A :⇒*: K)   (neK : Neutral K)
--           (D₁ : Γ ⊢ A :⇒*: K₁) (neK₁ : Neutral K₁)
--       → Tactic Γ A ⁰ ⁰ (ne D neK) (ne D₁ neK₁)
--   Π⁰⁰ : ∀ {A F G F₁ G₁}
--           (D : Γ ⊢ A :⇒*: Π F ▹ G) (⊢F : Γ ⊢ F) (⊢G : Γ ∙ F ⊢ G)
--           ([F] : wk-prop⁰ Γ F) ([G] : wk-subst-prop⁰ Γ F G [F])
--           (G-ext : wk-substEq-prop⁰ Γ F G [F] [G])
--           (D₁ : Γ ⊢ A :⇒*: Π F₁ ▹ G₁) (⊢F₁ : Γ ⊢ F₁) (⊢G₁ : Γ ∙ F₁ ⊢ G₁)
--           ([F]₁ : wk-prop⁰ Γ F₁)  ([G]₁ : wk-subst-prop⁰ Γ F₁ G₁ [F]₁)
--           (G-ext₁ : wk-substEq-prop⁰ Γ F₁ G₁ [F]₁ [G]₁)
--       → Tactic Γ A ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
--   Π⁰¹ : ∀ {F G F₁ G₁}
--           (D : Γ ⊢ Π F₁ ▹ G₁ :⇒*: Π F ▹ G) (⊢F : Γ ⊢ F) (⊢G : Γ ∙ F ⊢ G)
--           ([F] : wk-prop⁰ Γ F) ([G] : wk-subst-prop⁰ Γ F G [F])
--           (G-ext : wk-substEq-prop⁰ Γ F G [F] [G])
--           (⊢F₁ : Γ ⊢ F₁) (⊢G₁ : Γ ∙ F₁ ⊢ G₁) (⊩F₁ : Γ ⊩¹ F₁)
--           ([F]₁ : wk-prop¹ Γ F₁)  ([G]₁ : wk-subst-prop¹ Γ F₁ G₁ [F]₁)
--           (G-ext₁ : wk-substEq-prop¹ Γ F₁ G₁ [F]₁ [G]₁)
--       → Tactic Γ (Π F₁ ▹ G₁) ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁)
--   Π¹⁰ : ∀ {F G F₁ G₁}
--           (⊢F : Γ ⊢ F) (⊢G : Γ ∙ F ⊢ G) (⊩F : Γ ⊩¹ F)
--           ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F])
--           (G-ext : wk-substEq-prop¹ Γ F G [F] [G])
--           (D₁ : Γ ⊢ Π F ▹ G :⇒*: Π F₁ ▹ G₁) (⊢F₁ : Γ ⊢ F₁) (⊢G₁ : Γ ∙ F₁ ⊢ G₁)
--           ([F]₁ : wk-prop⁰ Γ F₁)  ([G]₁ : wk-subst-prop⁰ Γ F₁ G₁ [F]₁)
--           (G-ext₁ : wk-substEq-prop⁰ Γ F₁ G₁ [F]₁ [G]₁)
--       → Tactic Γ (Π F ▹ G) ¹ ⁰ (Π ⊢F ⊢G ⊩F [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
--   Π¹¹ : ∀ {F G}
--           (⊢F : Γ ⊢ F) (⊢G : Γ ∙ F ⊢ G) (⊩F : Γ ⊩¹ F)
--           ([F] : wk-prop¹ Γ F) ([G] : wk-subst-prop¹ Γ F G [F])
--           (G-ext : wk-substEq-prop¹ Γ F G [F] [G])
--           (⊢F₁ : Γ ⊢ F) (⊢G₁ : Γ ∙ F ⊢ G) (⊩F₁ : Γ ⊩¹ F)
--           ([F]₁ : wk-prop¹ Γ F) ([G]₁ : wk-subst-prop¹ Γ F G [F]₁)
--           (G-ext₁ : wk-substEq-prop¹ Γ F G [F]₁ [G]₁)
--       → Tactic Γ (Π F ▹ G) ¹ ¹ (Π ⊢F ⊢G ⊩F [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁)
--   U : Tactic Γ U ¹ ¹ U U
--   emb⁰¹ : ∀ {A l p q} → Tactic Γ A ⁰ l p q → Tactic Γ A ¹ l (emb p) q
--   emb¹⁰ : ∀ {A l p q} → Tactic Γ A l ⁰ p q → Tactic Γ A l ¹ p (emb q)


-- emb⁰¹ᵣ : ∀ {Γ A l p q} → Tactic Γ A l ¹ p (emb q) → Tactic Γ A l ⁰ p q
-- emb⁰¹ᵣ (emb⁰¹ t) = emb⁰¹ (emb⁰¹ᵣ t)
-- emb⁰¹ᵣ (emb¹⁰ t) = t

-- emb¹⁰ᵣ : ∀ {Γ A l p q} → Tactic Γ A ¹ l (emb p) q → Tactic Γ A ⁰ l p q
-- emb¹⁰ᵣ (emb⁰¹ t) = t
-- emb¹⁰ᵣ (emb¹⁰ t) = emb¹⁰ (emb¹⁰ᵣ t)

-- decRel : ∀ {Γ A} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A) → Dec (Tactic Γ A l l' p q)
-- decRel ⁰ ⁰ (ℕ D) (ℕ D₁) = yes (ℕ⁰⁰ D D₁)
-- decRel ⁰ ⁰ (ℕ D) (ne D₁ neK) = no (λ ())
-- decRel ⁰ ⁰ (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) = no (λ ())
-- decRel ⁰ ⁰ (ne D neK) (ℕ D₁) = no (λ ())
-- decRel ⁰ ⁰ (ne D neK) (ne D₁ neK₁) = yes (ne D neK D₁ neK₁)
-- decRel ⁰ ⁰ (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) = no (λ ())
-- decRel ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) = no (λ ())
-- decRel ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) = no (λ ())
-- decRel ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) = yes (Π⁰⁰ D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
-- decRel ⁰ ¹ (ℕ D) U = no (λ ())
-- decRel ⁰ ¹ (ℕ D) (ℕ ⊢Γ) = yes (ℕ⁰¹ D ⊢Γ)
-- decRel ⁰ ¹ (ℕ D) (Π ⊢F ⊢G q [F] [G] G-ext) = no (λ ())
-- decRel ⁰ ¹ (ne D neK) U = no (λ ())
-- decRel ⁰ ¹ (ne D neK) (ℕ ⊢Γ) = no (λ ())
-- decRel ⁰ ¹ (ne D neK) (Π ⊢F ⊢G q [F] [G] G-ext) = no (λ ())
-- decRel ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U = no (λ ())
-- decRel ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ ⊢Γ) = no (λ ())
-- decRel ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) = yes (Π⁰¹ D ⊢F ⊢G [F] [G] G-ext ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁)
-- decRel ⁰ ¹ p (emb x) with decRel ⁰ ⁰ p x
-- decRel ⁰ ¹ p (emb x) | yes p₁ = yes (emb¹⁰ p₁)
-- decRel ⁰ ¹ p (emb x) | no ¬p = no (λ x₁ → ¬p (emb⁰¹ᵣ x₁))
-- decRel ¹ ⁰ U (ℕ D) = no (λ ())
-- decRel ¹ ⁰ U (ne D neK) = no (λ ())
-- decRel ¹ ⁰ U (Π D ⊢F ⊢G [F] [G] G-ext) = no (λ ())
-- decRel ¹ ⁰ (ℕ ⊢Γ) (ℕ D) = yes (ℕ¹⁰ ⊢Γ D)
-- decRel ¹ ⁰ (ℕ ⊢Γ) (ne D neK) = no (λ ())
-- decRel ¹ ⁰ (ℕ ⊢Γ) (Π D ⊢F ⊢G [F] [G] G-ext) = no (λ ())
-- decRel ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ℕ D) = no (λ ())
-- decRel ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ne D neK) = no (λ ())
-- decRel ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) = yes (Π¹⁰ ⊢F ⊢G p [F] [G] G-ext D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
-- decRel ¹ ⁰ (emb x) q with decRel ⁰ ⁰ x q
-- decRel ¹ ⁰ (emb x) q | yes p = yes (emb⁰¹ p)
-- decRel ¹ ⁰ (emb x) q | no ¬p = no (λ x₁ → ¬p (emb¹⁰ᵣ x₁))
-- decRel ¹ ¹ U U = yes U
-- decRel ¹ ¹ (ℕ ⊢Γ) (ℕ ⊢Γ₁) = yes (ℕ¹¹ ⊢Γ ⊢Γ₁)
-- decRel ¹ ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) = yes (Π¹¹ ⊢F ⊢G p [F] [G] G-ext ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁)
-- decRel ¹ ¹ p (emb x) with decRel ¹ ⁰ p x
-- decRel ¹ ¹ p (emb x) | yes p₁ = yes (emb¹⁰ p₁)
-- decRel ¹ ¹ p (emb x) | no ¬p = no (λ x₁ → ¬p (emb⁰¹ᵣ x₁))
-- decRel ¹ ¹ (emb x) q with decRel ⁰ ¹ x q
-- decRel ¹ ¹ (emb x) q | yes p = yes (emb⁰¹ p)
-- decRel ¹ ¹ (emb x) q | no ¬p = no (λ x₁ → ¬p (emb¹⁰ᵣ x₁))

-- refuteRel : ∀ {Γ A} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A) → (Tactic Γ A l l' p q → ⊥) → ⊥
-- refuteRel ⁰ ⁰ (ℕ D) (ℕ D₁) prf = prf (ℕ⁰⁰ D D₁)
-- refuteRel ⁰ ⁰ (ℕ D) (ne D₁ neK) prf = ℕ≢ne neK (whrDet*' (red D , ℕ) (red D₁ , (ne neK)))
-- refuteRel ⁰ ⁰ (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) prf = ℕ≢Π (whrDet*' (red D , ℕ) (red D₁ , Π))
-- refuteRel ⁰ ⁰ (ne D neK) (ℕ D₁) prf = ℕ≢ne neK (whrDet*' (red D₁ , ℕ) (red D , (ne neK)))
-- refuteRel ⁰ ⁰ (ne D neK) (ne D₁ neK₁) prf = prf (ne D neK D₁ neK₁)
-- refuteRel ⁰ ⁰ (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) prf = Π≢ne neK (whrDet*' (red D₁ , Π) (red D , (ne neK)))
-- refuteRel ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) prf = ℕ≢Π (whrDet*' (red D₁ , ℕ) (red D , Π))
-- refuteRel ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) prf = Π≢ne neK (whrDet*' (red D , Π) (red D₁ , (ne neK)))
-- refuteRel ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) prf = prf (Π⁰⁰ D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
-- refuteRel ⁰ ¹ (ℕ D) U prf = U≢ℕ (whnfRed*' (red D) U)
-- refuteRel ⁰ ¹ (ℕ D) (ℕ ⊢Γ) prf = prf (ℕ⁰¹ D ⊢Γ)
-- refuteRel ⁰ ¹ (ℕ D) (Π ⊢F ⊢G q [F] [G] G-ext) prf = ℕ≢Π (PE.sym (whnfRed*' (red D) Π))
-- refuteRel ⁰ ¹ (ne D neK) U prf = U≢ne neK (whnfRed*' (red D) U)
-- refuteRel ⁰ ¹ (ne D neK) (ℕ ⊢Γ) prf = ℕ≢ne neK (whnfRed*' (red D) ℕ)
-- refuteRel ⁰ ¹ (ne D neK) (Π ⊢F ⊢G q [F] [G] G-ext) prf = Π≢ne neK (whnfRed*' (red D) Π)
-- refuteRel ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U prf = U≢Π (whnfRed*' (red D) U)
-- refuteRel ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ ⊢Γ) prf = ℕ≢Π (whnfRed*' (red D) ℕ)
-- refuteRel ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) prf = prf (Π⁰¹ D ⊢F ⊢G [F] [G] G-ext ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁)
-- refuteRel ⁰ ¹ p (emb x) prf = refuteRel ⁰ ⁰ p x (λ z → prf (emb¹⁰ z))
-- refuteRel ¹ ⁰ U (ℕ D) prf = U≢ℕ (whnfRed*' (red D) U)
-- refuteRel ¹ ⁰ U (ne D neK) prf = U≢ne neK (whnfRed*' (red D) U)
-- refuteRel ¹ ⁰ U (Π D ⊢F ⊢G [F] [G] G-ext) prf = U≢Π (whnfRed*' (red D) U)
-- refuteRel ¹ ⁰ (ℕ ⊢Γ) (ℕ D) prf = prf (ℕ¹⁰ ⊢Γ D)
-- refuteRel ¹ ⁰ (ℕ ⊢Γ) (ne D neK) prf = ℕ≢ne neK (whnfRed*' (red D) ℕ)
-- refuteRel ¹ ⁰ (ℕ ⊢Γ) (Π D ⊢F ⊢G [F] [G] G-ext) prf = ℕ≢Π (whnfRed*' (red D) ℕ)
-- refuteRel ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ℕ D) prf = ℕ≢Π (PE.sym (whnfRed*' (red D) Π))
-- refuteRel ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ne D neK) prf = Π≢ne neK (whnfRed*' (red D) Π)
-- refuteRel ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) prf = prf (Π¹⁰ ⊢F ⊢G p [F] [G] G-ext D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
-- refuteRel ¹ ⁰ (emb x) q prf = refuteRel ⁰ ⁰ x q (λ z → prf (emb⁰¹ z))
-- refuteRel ¹ ¹ U U prf = prf U
-- refuteRel ¹ ¹ (ℕ ⊢Γ) (ℕ ⊢Γ₁) prf = prf (ℕ¹¹ ⊢Γ ⊢Γ₁)
-- refuteRel ¹ ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) prf = prf (Π¹¹ ⊢F ⊢G p [F] [G] G-ext ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁)
-- refuteRel ¹ ¹ p (emb x) prf = refuteRel ¹ ⁰ p x (λ z → prf (emb¹⁰ z))
-- refuteRel ¹ ¹ (emb x) q prf = refuteRel ⁰ ¹ x q (λ z → prf (emb⁰¹ z))
