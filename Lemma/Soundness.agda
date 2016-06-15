module Lemma.Soundness where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


soundness : ∀ {l Γ A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
soundness (U ⊢Γ) = U ⊢Γ
soundness (ℕ [ ⊢A , ⊢B , D ]) = ⊢A
soundness (ne [ ⊢A , ⊢B , D ] neK) = ⊢A
soundness (Π [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) = ⊢A
soundness {⁰} (emb {l< = ()} x)
soundness {¹} (emb {l< = 0<1} x) = soundness x

soundnessEq : ∀ {l Γ A B} → ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊢ A ≡ B
soundnessEq (U ⊢Γ) PE.refl = refl (U ⊢Γ)
soundnessEq (ℕ D) A≡B = trans (subset* (red D)) (sym (subset* A≡B))
soundnessEq (ne D neK) ne[ M , D' , neM , K≡M ] = trans (subset* (red D)) (trans K≡M (sym (subset* (red D'))))
soundnessEq (Π D ⊢F ⊢G [F] [G] G-ext) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = A≡B
soundnessEq {⁰} (emb {l< = ()} x) A≡B
soundnessEq {¹} (emb {l< = 0<1} x) A≡B = soundnessEq x A≡B

soundnessTerm : ∀ {l Γ A t} → ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊢ t ∷ A
soundnessTerm (U ⊢Γ) (⊢t , ⊩t) = ⊢t
soundnessTerm (ℕ D) ℕ[ n , [ ⊢t , ⊢u , d ] , natN ] = conv ⊢t (sym (subset* (red D)))
soundnessTerm (ne D neK) t = t
soundnessTerm (Π D ⊢F ⊢G [F] [G] G-ext) (⊢t , [t]) = ⊢t
soundnessTerm {⁰} (emb {l< = ()} x) t
soundnessTerm {¹} (emb {l< = 0<1} x) t = soundnessTerm x t

soundnessTermEq : ∀ {l Γ A t u} → ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊢ t ≡ u ∷ A
soundnessTermEq (U ⊢Γ) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = t≡u
soundnessTermEq (ℕ D) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = conv t≡u (sym (subset* (red D)))
soundnessTermEq (ne D neK) t≡u = t≡u
soundnessTermEq (Π D ⊢F ⊢G [F] [G] G-ext) (t≡u , ⊩t , ⊩u , [t≡u]) = t≡u
soundnessTermEq {⁰} (emb {l< = ()} x) t≡u
soundnessTermEq {¹} (emb {l< = 0<1} x) t≡u = soundnessTermEq x t≡u

-- soundness : ∀ {Γ A} T → ⊢ Γ → Γ ⊩⟨ T ⟩ A → Γ ⊢ A
-- soundness ⁰ ⊢Γ (ℕ [ Γ⊢A , Γ⊢B , A⇒*B ]) = Γ⊢A
-- soundness ⁰ ⊢Γ (ne [ Γ⊢A , Γ⊢B , A⇒*B ] neK) = Γ⊢A
-- soundness ⁰ ⊢Γ (Π [ Γ⊢A , Γ⊢B , A⇒*B ] x₁ x₂ [F] [G] x₃) = Γ⊢A
-- soundness ¹ ⊢Γ U = U ⊢Γ
-- soundness ¹ ⊢Γ (ℕ ⊢Γ₁) = ℕ ⊢Γ
-- soundness ¹ ⊢Γ (Π x x₁ A [F] [G] x₂) = Π x ▹ x₁
-- soundness ¹ ⊢Γ (emb x) = soundness ⁰ ⊢Γ x

-- soundnessEq : ∀ {Γ A B} T → ⊢ Γ → ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ A ≡ B / [A] → Γ ⊢ A ≡ B
-- soundnessEq ⁰ ⊢Γ (ℕ [ Γ⊢A , Γ⊢B , A⇒*B ]) x₁ = trans (subset* A⇒*B) (sym (subset* x₁))
-- soundnessEq ⁰ ⊢Γ (ne [ ⊢A , ⊢B , D ] neK) ne[ M , [ ⊢A₁ , ⊢B₁ , D₁ ] , neM , K≡M ] = trans (subset* D) (trans K≡M (sym (subset* D₁)))
-- soundnessEq ⁰ ⊢Γ (Π x x₁ x₂ [F] [G] x₃) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = A≡B
-- soundnessEq ¹ ⊢Γ U x = PE.subst (λ x → _ ⊢ _ ≡ x) (PE.sym x) (refl (U ⊢Γ))
-- soundnessEq ¹ ⊢Γ (ℕ ⊢Γ₁) x = sym (subset* x)
-- soundnessEq ¹ ⊢Γ (Π ⊢F ⊢G [A] [F] [G] G-ext) Π¹[ F' , G' , ΠFG≡ΠF'G' , t≡ΠF'G' , [F≡F'] , [G≡G'] ] = t≡ΠF'G'
-- soundnessEq ¹ ⊢Γ (emb x) x₁ = soundnessEq ⁰ ⊢Γ x x₁

-- soundnessTerm : ∀ {Γ A t} T → ⊢ Γ → ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ∷ A / [A] → Γ ⊢ t ∷ A
-- soundnessTerm ⁰ ⊢Γ (ℕ [ ⊢A , ⊢B , D ]) ℕ[ n , [ ⊢t , ⊢u , d ] , natN ] = conv ⊢t (sym (subset* D))
-- soundnessTerm ⁰ ⊢Γ (ne x x₁) t₁ = t₁
-- soundnessTerm ⁰ ⊢Γ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂) = proj₁
-- soundnessTerm ¹ ⊢Γ U (proj₁ , proj₂) = proj₁
-- soundnessTerm ¹ ⊢Γ (ℕ ⊢Γ₁) ℕ[ n , [ ⊢t , ⊢u , d ] , natN ] = ⊢t
-- soundnessTerm ¹ ⊢Γ (Π x x₁ [A] [F] [G] x₂) (proj₁ , proj₂) = proj₁
-- soundnessTerm ¹ ⊢Γ (emb x) t₁ = soundnessTerm ⁰ ⊢Γ x t₁

-- soundnessTermEq : ∀ {Γ A t u} T → ⊢ Γ → ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ≡ u ∷ A / [A] → Γ ⊢ t ≡ u ∷ A
-- soundnessTermEq ⁰ ⊢Γ (ℕ [ ⊢A , ⊢B , D ]) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = conv t≡u (sym (subset* D))
-- soundnessTermEq ⁰ ⊢Γ (ne x x₁) t≡u = t≡u
-- soundnessTermEq ⁰ ⊢Γ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂ , proj₃ , proj₄) = proj₁
-- soundnessTermEq ¹ ⊢Γ U U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = t≡u
-- soundnessTermEq ¹ ⊢Γ (ℕ ⊢Γ₁) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = t≡u
-- soundnessTermEq ¹ ⊢Γ (Π x x₁ [A] [F] [G] x₂) (proj₁ , proj₂ , proj₃ , proj₄) = proj₁
-- soundnessTermEq ¹ ⊢Γ (emb x) t≡u = soundnessTermEq ⁰ ⊢Γ x t≡u
