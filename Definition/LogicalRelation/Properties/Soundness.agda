module Definition.LogicalRelation.Properties.Soundness where

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
soundnessTerm (ℕ D) ℕ[ n , [ ⊢t , ⊢u , d ] , natN , prop ] = conv ⊢t (sym (subset* (red D)))
soundnessTerm (ne D neK) t = t
soundnessTerm (Π D ⊢F ⊢G [F] [G] G-ext) (⊢t , [t]) = ⊢t
soundnessTerm {⁰} (emb {l< = ()} x) t
soundnessTerm {¹} (emb {l< = 0<1} x) t = soundnessTerm x t

soundnessTermEq : ∀ {l Γ A t u} → ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊢ t ≡ u ∷ A
soundnessTermEq (U ⊢Γ) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = t≡u
soundnessTermEq (ℕ D) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ] = conv t≡u (sym (subset* (red D)))
soundnessTermEq (ne D neK) t≡u = t≡u
soundnessTermEq (Π D ⊢F ⊢G [F] [G] G-ext) (t≡u , ⊩t , ⊩u , [t≡u]) = t≡u
soundnessTermEq {⁰} (emb {l< = ()} x) t≡u
soundnessTermEq {¹} (emb {l< = 0<1} x) t≡u = soundnessTermEq x t≡u
