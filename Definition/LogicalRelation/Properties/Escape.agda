{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Escape {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Reducible types are well-formed.
escape : ∀ {l A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
escape (Uᵣ′ l′ l< ⊢Γ) = Uⱼ ⊢Γ
escape (ℕᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Emptyᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Unitᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Bᵣ′ W F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
escape (emb 0<1 A) = escape A

-- Reducible type equality respect the equality relation.
escapeEq : ∀ {l A B} → ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊢ A ≅ B
escapeEq (Uᵣ′ l′ l< ⊢Γ) PE.refl = ≅-Urefl ⊢Γ
escapeEq (ℕᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ ℕₙ ℕₙ (≅-ℕrefl (wf ⊢A))
escapeEq (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
escapeEq (Unitᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Unitₙ Unitₙ (≅-Unitrefl (wf ⊢A))
escapeEq (ne′ K D neK K≡K) (ne₌ M D′ neM K≡M) =
  ≅-red (red D) (red D′) (ne neK) (ne neM) (~-to-≅ K≡M)
escapeEq (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
             (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ≅-red (red D) D′ ⟦ W ⟧ₙ ⟦ W ⟧ₙ A≡B
escapeEq (emb 0<1 A) A≡B = escapeEq A A≡B

-- Reducible terms are well-formed.
escapeTerm : ∀ {l A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
escapeTerm (Uᵣ′ l′ l< ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) = ⊢t
escapeTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Emptyᵣ D) (Emptyₜ e [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Unitᵣ D) (Unitₜ e [ ⊢t , ⊢u , d ] prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (Πₜ f [ ⊢t , ⊢u , d ] funcF f≡f [f] [f]₁) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (Σₜ p [ ⊢t , ⊢u , d ] pProd p≅p [fst] [snd]) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (emb 0<1 A) t = escapeTerm A t

-- Reducible term equality respect the equality relation.
escapeTermEq : ∀ {l A t u} → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
                → Γ ⊢ t ≅ u ∷ A
escapeTermEq (Uᵣ′ l′ l< ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red (id (Uⱼ ⊢Γ)) (redₜ d) (redₜ d′) Uₙ (typeWhnf typeA) (typeWhnf typeB) A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ℕₙ
             (naturalWhnf natK) (naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = esplit prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Emptyₙ
             (ne natK) (ne natK′) k≡k′
escapeTermEq {l} {Γ} {A} {t} {u} (Unitᵣ D) (Unitₜ₌ ⊢t ⊢u) =
  let t≅u = ≅ₜ-η-unit ⊢t ⊢u
      A≡Unit = subset* (red D)
  in  ≅-conv t≅u (sym A≡Unit)
escapeTermEq (ne′ K D neK K≡K)
                 (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
         (~-to-≅ₜ t≡u)
escapeTermEq (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Πₙ (functionWhnf funcF) (functionWhnf funcG) f≡g
escapeTermEq (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡]) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Σₙ (productWhnf pProd) (productWhnf rProd) p≅r
escapeTermEq (emb 0<1 A) t≡u = escapeTermEq A t≡u
