module Definition.LogicalRelation.Properties.Soundness where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


soundness : ∀ {l Γ A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
soundness (U (U l' l< ⊢Γ)) = U ⊢Γ
soundness (ℕ (ℕ [ ⊢A , ⊢B , D ])) = ⊢A
soundness (ne (ne K [ ⊢A , ⊢B , D ] neK)) = ⊢A
soundness (Π (Π F G [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext)) = ⊢A
soundness (emb {l< = 0<1} x) = soundness x

soundnessEq : ∀ {l Γ A B} → ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊢ A ≡ B
soundnessEq (U (U l' l< ⊢Γ)) PE.refl = refl (U ⊢Γ)
soundnessEq (ℕ (ℕ D)) A≡B = trans (subset* (red D)) (sym (subset* A≡B))
soundnessEq (ne (ne K D neK)) ne[ M , D' , neM , K≡M ] = trans (subset* (red D)) (trans K≡M (sym (subset* (red D'))))
soundnessEq (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = A≡B
soundnessEq (emb {l< = 0<1} x) A≡B = soundnessEq x A≡B

soundnessTerm : ∀ {l Γ A t} → ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊢ t ∷ A
soundnessTerm (U (U l' l< ⊢Γ)) (⊢t , ⊩t) = ⊢t
soundnessTerm (ℕ (ℕ D)) ℕ[ n , [ ⊢t , ⊢u , d ] , natN , prop ] = conv ⊢t (sym (subset* (red D)))
soundnessTerm (ne (ne K D neK)) t = t
soundnessTerm (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (⊢t , [t]) = ⊢t
soundnessTerm (emb {l< = 0<1} x) t = soundnessTerm x t

soundnessTermEq : ∀ {l Γ A t u} → ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊢ t ≡ u ∷ A
soundnessTermEq (U (U l' l< ⊢Γ)) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = t≡u
soundnessTermEq (ℕ (ℕ D)) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ] = conv t≡u (sym (subset* (red D)))
soundnessTermEq (ne (ne K D neK)) t≡u = t≡u
soundnessTermEq (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (t≡u , ⊩t , ⊩u , [t≡u]) = t≡u
soundnessTermEq (emb {l< = 0<1} x) t≡u = soundnessTermEq x t≡u
