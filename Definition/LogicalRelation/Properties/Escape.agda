{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Escape {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Reducible types are well-formed.
escape : ∀ {l Γ A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
escape (U′ l′ l< ⊢Γ) = U ⊢Γ
escape (ℕ [ ⊢A , ⊢B , D ]) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Π′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
escape (emb 0<1 A) = escape A

-- Reducible type equality respect the equality relation.
escapeEq : ∀ {l Γ A B} → ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊢ A ≅ B
escapeEq (U′ l′ l< ⊢Γ) PE.refl = ≅-Urefl ⊢Γ
escapeEq (ℕ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ ℕ ℕ (≅-ℕrefl (wf ⊢A))
escapeEq (ne′ K D neK K≡K) (ne₌ M D′ neM K≡M) =
  ≅-red (red D) (red D′) (ne neK) (ne neM) (~-to-≅ K≡M)
escapeEq (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ≅-red (red D) D′ Π Π A≡B
escapeEq (emb 0<1 A) A≡B = escapeEq A A≡B

-- Reducible terms are well-formed.
escapeTerm : ∀ {l Γ A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
escapeTerm (U (U l′ l< ⊢Γ)) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) = ⊢t
escapeTerm (ℕ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (f , [ ⊢t , ⊢u , d ] , funcF , f≡f , [f] , [f]₁) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (emb 0<1 A) t = escapeTerm A t

-- Reducible term equality respect the equality relation.
escapeTermEq : ∀ {l Γ A t u} → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
                → Γ ⊢ t ≅ u ∷ A
escapeTermEq (U (U l′ l< ⊢Γ)) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red (id (U ⊢Γ)) (redₜ d) (redₜ d′) U (typeWhnf typeA) (typeWhnf typeB) A≡B
escapeTermEq (ℕ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ℕ
             (naturalWhnf natK) (naturalWhnf natK′) k≡k′
escapeTermEq (ne′ K D neK K≡K)
                 (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
         (~-to-≅ₜ t≡u)
escapeTermEq (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Π (functionWhnf funcF) (functionWhnf funcG) f≡g
escapeTermEq (emb 0<1 A) t≡u = escapeTermEq A t≡u
