module Definition.LogicalRelation.Properties.Wellformed where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE


wellformed : ∀ {l Γ A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
wellformed (U' l' l< ⊢Γ) = U ⊢Γ
wellformed (ℕ [ ⊢A , ⊢B , D ]) = ⊢A
wellformed (ne' K [ ⊢A , ⊢B , D ] neK) = ⊢A
wellformed (Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) = ⊢A
wellformed (emb 0<1 A) = wellformed A

wellformedEq : ∀ {l Γ A B} → ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊢ A ≡ B
wellformedEq (U' l' l< ⊢Γ) PE.refl = refl (U ⊢Γ)
wellformedEq (ℕ D) A≡B = trans (subset* (red D)) (sym (subset* A≡B))
wellformedEq (ne' K D neK) (ne₌ M D' neM K≡M) =
  trans (subset* (red D)) (trans K≡M (sym (subset* (red D'))))
wellformedEq (Π' F G D ⊢F ⊢G [F] [G] G-ext)
             (Π₌ F' G' D' A≡B [F≡F'] [G≡G']) = A≡B
wellformedEq (emb 0<1 A) A≡B = wellformedEq A A≡B

wellformedTerm : ∀ {l Γ A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
wellformedTerm (U' l' l< ⊢Γ) (Uₜ ⊢t ⊩t) = ⊢t
wellformedTerm (ℕ D) (ℕₜ n [ ⊢t , ⊢u , d ] natN prop) =
  conv ⊢t (sym (subset* (red D)))
wellformedTerm (ne' K D neK) t = t
wellformedTerm (Π' F G D ⊢F ⊢G [F] [G] G-ext) (Πₜ ⊢t [t] [t]₁) = ⊢t
wellformedTerm (emb 0<1 A) t = wellformedTerm A t

wellformedTermEq : ∀ {l Γ A t u} → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
                → Γ ⊢ t ≡ u ∷ A
wellformedTermEq (U' l' l< ⊢Γ) (Uₜ₌ ⊢t ⊢u t≡u ⊩t ⊩u [t≡u]) = t≡u
wellformedTermEq (ℕ D) (ℕₜ₌ k k' d d' t≡u prop) =
  conv t≡u (sym (subset* (red D)))
wellformedTermEq (ne' K D neK) t≡u = t≡u
wellformedTermEq (Π' F G D ⊢F ⊢G [F] [G] G-ext) (Πₜ₌ t≡u ⊩t ⊩u [t≡u]) = t≡u
wellformedTermEq (emb 0<1 A) t≡u = wellformedTermEq A t≡u
