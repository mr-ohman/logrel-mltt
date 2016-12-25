{-# OPTIONS --without-K #-}

open import Definition.EqualityRelation

module Definition.LogicalRelation.Properties.Wellformed {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE


wellformed : ∀ {l Γ A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
wellformed (U' l' l< ⊢Γ) = U ⊢Γ
wellformed (ℕ [ ⊢A , ⊢B , D ]) = ⊢A
wellformed (ne' K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
wellformed (Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
wellformed (emb 0<1 A) = wellformed A

wellformedEq : ∀ {l Γ A B} → ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊢ A ≅ B
wellformedEq (U' l' l< ⊢Γ) PE.refl = ≅-Urefl ⊢Γ
wellformedEq (ℕ [ ⊢A , ⊢B , D ]) D' = ≅-red D D' (≅-ℕrefl (wf ⊢A))
wellformedEq (ne' K D neK K≡K) (ne₌ M D' neM K≡M) =
  ≅-red (red D) (red D') K≡M
wellformedEq (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
             (Π₌ F' G' D' A≡B [F≡F'] [G≡G']) = A≡B
wellformedEq (emb 0<1 A) A≡B = wellformedEq A A≡B

wellformedTerm : ∀ {l Γ A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
wellformedTerm (U (U l' l< ⊢Γ)) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) = ⊢t
wellformedTerm (ℕ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t natN prop) =
  conv ⊢t (sym (subset* (red D)))
wellformedTerm (ne' K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) = ⊢t
wellformedTerm (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext))
               (f , [ ⊢t , ⊢u , d ] , funcF , f≡f , [f] , [f]₁) = ⊢t
wellformedTerm (emb 0<1 A) t = wellformedTerm A t

wellformedTermEq : ∀ {l Γ A t u} → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
                → Γ ⊢ t ≅ u ∷ A
wellformedTermEq (U (U l' l< ⊢Γ)) (Uₜ₌ A B d d' typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red (id (U ⊢Γ)) (redₜ d) (redₜ d') A≡B
wellformedTermEq (ℕ D) (ℕₜ₌ k k' d d' k≡k' prop) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d') k≡k'
wellformedTermEq (ne' K [ ⊢A , ⊢B , D ] neK K≡K)
                 (neₜ₌ k m d d' (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (id ⊢A) (redₜ d) (redₜ d') t≡u
wellformedTermEq (Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Πₜ₌ f g d d' funcF funcG f≡g [f] [g] [f≡g]) =
  f≡g
wellformedTermEq (emb 0<1 A) t≡u = wellformedTermEq A t≡u
