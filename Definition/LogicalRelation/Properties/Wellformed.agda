module Definition.LogicalRelation.Properties.Wellformed where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


wellformed : ∀ {l Γ A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
wellformed (U (U l' l< ⊢Γ)) = U ⊢Γ
wellformed (ℕ (ℕ [ ⊢A , ⊢B , D ])) = ⊢A
wellformed (ne (ne K [ ⊢A , ⊢B , D ] neK)) = ⊢A
wellformed (Π (Π F G [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext)) = ⊢A
wellformed (emb {l< = 0<1} x) = wellformed x

wellformedEq : ∀ {l Γ A B} → ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊢ A ≡ B
wellformedEq (U (U l' l< ⊢Γ)) PE.refl = refl (U ⊢Γ)
wellformedEq (ℕ (ℕ D)) A≡B = trans (subset* (red D)) (sym (subset* A≡B))
wellformedEq (ne (ne K D neK)) ne[ M , D' , neM , K≡M ] =
  trans (subset* (red D)) (trans K≡M (sym (subset* (red D'))))
wellformedEq (Π (Π F G D ⊢F ⊢G [F] [G] G-ext))
            Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = A≡B
wellformedEq (emb {l< = 0<1} x) A≡B = wellformedEq x A≡B

wellformedTerm : ∀ {l Γ A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
wellformedTerm (U (U l' l< ⊢Γ)) (⊢t , ⊩t) = ⊢t
wellformedTerm (ℕ (ℕ D)) ℕ[ n , [ ⊢t , ⊢u , d ] , natN , prop ] =
  conv ⊢t (sym (subset* (red D)))
wellformedTerm (ne (ne K D neK)) t = t
wellformedTerm (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (⊢t , [t]) = ⊢t
wellformedTerm (emb {l< = 0<1} x) t = wellformedTerm x t

wellformedTermEq : ∀ {l Γ A t u} → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
                → Γ ⊢ t ≡ u ∷ A
wellformedTermEq (U (U l' l< ⊢Γ)) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = t≡u
wellformedTermEq (ℕ (ℕ D)) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ] =
  conv t≡u (sym (subset* (red D)))
wellformedTermEq (ne (ne K D neK)) t≡u = t≡u
wellformedTermEq (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (t≡u , ⊩t , ⊩u , [t≡u]) = t≡u
wellformedTermEq (emb {l< = 0<1} x) t≡u = wellformedTermEq x t≡u
