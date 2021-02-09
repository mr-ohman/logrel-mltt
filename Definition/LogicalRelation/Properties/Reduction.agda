{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reduction {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped using (Con ; Term)
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Wk
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Universe
open import Definition.LogicalRelation.Properties.Escape

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Weak head expansion of reducible types.
redSubst* : ∀ {A B l}
          → Γ ⊢ A ⇒* B
          → Γ ⊩⟨ l ⟩ B
          → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst* D (Uᵣ′ l′ l< ⊢Γ) rewrite redU* D =
  Uᵣ′ l′ l< ⊢Γ , PE.refl
redSubst* D (ℕᵣ [ ⊢B , ⊢ℕ , D′ ]) =
  let ⊢A = redFirst* D
  in  ℕᵣ ([ ⊢A , ⊢ℕ , D ⇨* D′ ]) , D′
redSubst* D (Emptyᵣ [ ⊢B , ⊢Empty , D′ ]) =
  let ⊢A = redFirst* D
  in  Emptyᵣ ([ ⊢A , ⊢Empty , D ⇨* D′ ]) , D′
redSubst* D (Unitᵣ [ ⊢B , ⊢Unit , D′ ]) =
  let ⊢A = redFirst* D
  in  Unitᵣ ([ ⊢A , ⊢Unit , D ⇨* D′ ]) , D′
redSubst* D (ne′ K [ ⊢B , ⊢K , D′ ] neK K≡K) =
  let ⊢A = redFirst* D
  in  (ne′ K [ ⊢A , ⊢K , D ⇨* D′ ] neK K≡K)
  ,   (ne₌ _ [ ⊢B , ⊢K , D′ ] neK K≡K)
redSubst* D (Bᵣ′ W F G [ ⊢B , ⊢ΠFG , D′ ] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let ⊢A = redFirst* D
  in  (Bᵣ′ W F G [ ⊢A , ⊢ΠFG , D ⇨* D′ ] ⊢F ⊢G A≡A [F] [G] G-ext)
  ,   (B₌ _ _ D′ A≡A (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
        (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])))
redSubst* D (emb 0<1 x) with redSubst* D x
redSubst* D (emb 0<1 x) | y , y₁ = emb 0<1 y , y₁

-- Weak head expansion of reducible terms.
redSubst*Term : ∀ {A t u l}
              → Γ ⊢ t ⇒* u ∷ A
              → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ u ∷ A / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubst*Term t⇒u (Uᵣ′ .⁰ 0<1 ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [u]) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ redFirst*Term t⇒u , ⊢u , t⇒u ⇨∷* d ]
      q = redSubst* (univ* t⇒u) (univEq (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ A [d] typeA A≡A [u]))
  in Uₜ A [d′] typeA A≡A (proj₁ q)
  ,  Uₜ₌ A A [d′] [d] typeA typeA A≡A (proj₁ q) [u] (proj₂ q)
redSubst*Term t⇒u (ℕᵣ D) (ℕₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡ℕ  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡ℕ
      t⇒u′ = conv* t⇒u A≡ℕ
  in  ℕₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
  ,   ℕₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflNatural-prop prop)
redSubst*Term t⇒u (Emptyᵣ D) (Emptyₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡Empty  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡Empty
      t⇒u′ = conv* t⇒u A≡Empty
  in  Emptyₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
  ,   Emptyₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflEmpty-prop prop)
redSubst*Term t⇒u (Unitᵣ D) (Unitₜ n [ ⊢u , ⊢n , d ] prop) =
  let A≡Unit  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡Unit
      t⇒u′ = conv* t⇒u A≡Unit
  in  Unitₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] prop
  ,   Unitₜ₌ ⊢t ⊢u
redSubst*Term t⇒u (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k)) =
  let A≡K  = subset* (red D)
      [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ conv (redFirst*Term t⇒u) A≡K , ⊢u , conv* t⇒u A≡K ⇨∷* d ]
  in  neₜ k [d′] (neNfₜ neK₁ ⊢k k≡k) , neₜ₌ k k [d′] [d] (neNfₜ₌ neK₁ neK₁ k≡k)
redSubst*Term {A} {t} {u} {l} {Γ} t⇒u (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  [u]@(Πₜ f [d]@([ ⊢t , ⊢u , d ]) funcF f≡f [f] [f]₁) =
  let A≡ΠFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΠFG
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΠFG , ⊢u , conv* t⇒u A≡ΠFG ⇨∷* d ]
      [u′] = Πₜ f [d′] funcF f≡f [f] [f]₁
  in  [u′]
  ,   Πₜ₌ f f [d′] [d] funcF funcF f≡f [u′] [u]
          (λ [ρ] ⊢Δ [a] → reflEqTerm ([G] [ρ] ⊢Δ [a]) ([f]₁ [ρ] ⊢Δ [a]))
redSubst*Term {A} {t} {u} {l} {Γ} t⇒u (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  [u]@(Σₜ p [d]@([ ⊢t , ⊢u , d ]) pProd p≅p [fst] [snd]) =
  let A≡ΣFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΣFG
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΣFG , ⊢u , conv* t⇒u A≡ΣFG ⇨∷* d ]
      [u′] = Σₜ p [d′] pProd p≅p [fst] [snd]
  in  [u′]
  ,   Σₜ₌ p p [d′] [d] pProd pProd p≅p [u′] [u] [fst] [fst]
          (reflEqTerm ([F] Wk.id (wf ⊢F)) [fst])
          (reflEqTerm ([G] Wk.id (wf ⊢F) [fst]) [snd])
redSubst*Term t⇒u (emb 0<1 x) [u] = redSubst*Term t⇒u x [u]

-- Weak head expansion of reducible types with single reduction step.
redSubst : ∀ {A B l}
         → Γ ⊢ A ⇒ B
         → Γ ⊩⟨ l ⟩ B
         → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst A⇒B [B] = redSubst* (A⇒B ⇨ id (escape [B])) [B]

-- Weak head expansion of reducible terms with single reduction step.
redSubstTerm : ∀ {A t u l}
             → Γ ⊢ t ⇒ u ∷ A
             → ([A] : Γ ⊩⟨ l ⟩ A)
             → Γ ⊩⟨ l ⟩ u ∷ A / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A / [A]
             × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (t⇒u ⇨ id (escapeTerm [A] [u])) [A] [u]
