open import Definition.EqualityRelation

module Definition.LogicalRelation.Properties.Reduction {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Symmetry
open import Definition.LogicalRelation.Properties.Transitivity
open import Definition.LogicalRelation.Properties.Conversion
open import Definition.LogicalRelation.Properties.Universe
open import Definition.LogicalRelation.Properties.Wellformed

open import Tools.Product
open import Tools.Empty

import Tools.PropositionalEquality as PE


redSubst* : ∀ {A B l Γ}
          → Γ ⊢ A ⇒* B
          → _⊩⟨_⟩_ {{eqrel}} Γ l B
          → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst* D (U' l' l< ⊢Γ) rewrite redU* D =
  U (U l' l< ⊢Γ) , PE.refl
redSubst* D (ℕ [ ⊢B , ⊢ℕ , D' ]) =
  let ⊢A = redFirst* D
  in  ℕ ([ ⊢A , ⊢ℕ , D ⇨* D' ]) , D'
redSubst* D (ne' K [ ⊢B , ⊢K , D' ] neK K≡K) =
  let ⊢A = redFirst* D
  in  (ne' K [ ⊢A , ⊢K , D ⇨* D' ] neK K≡K)
  ,   (ne₌ _ [ ⊢B , ⊢K , D' ] neK K≡K)
redSubst* D (Π' F G [ ⊢B , ⊢ΠFG , D' ] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let ⊢A = redFirst* D
  in  (Π' F G [ ⊢A , ⊢ΠFG , D ⇨* D' ] ⊢F ⊢G (≅-red D D A≡A) [F] [G] G-ext)
  ,   (Π₌ _ _ D' (≅-red D (id ⊢B) A≡A) (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
        (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])))
redSubst* D (emb 0<1 x) with redSubst* D x
redSubst* D (emb 0<1 x) | y , y₁ = emb 0<1 y , y₁

redSubst*Term : ∀ {A t u l Γ}
              → Γ ⊢ t ⇒* u ∷ A
              → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ u ∷ A / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubst*Term t⇒u (U' .⁰ 0<1 ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [u]) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d'] = [ redFirst*Term t⇒u , ⊢u , t⇒u ⇨∷* d ]
      q = redSubst* (univ* t⇒u) (univEq (U' ⁰ 0<1 ⊢Γ) (Uₜ A [d] typeA A≡A [u]))
  in Uₜ A [d'] typeA A≡A (proj₁ q)
  ,  Uₜ₌ A A [d'] [d] typeA typeA A≡A (proj₁ q) [u] (proj₂ q)
redSubst*Term t⇒u (ℕ D) (ℕₜ n [ ⊢u , ⊢n , d ] n≡n natN prop) =
  let A≡ℕ  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡ℕ
      t⇒u' = conv* t⇒u A≡ℕ
  in  ℕₜ n [ ⊢t , ⊢n , t⇒u' ⇨∷* d ] n≡n natN prop
  ,   ℕₜ₌ n n [ ⊢t , ⊢n , t⇒u' ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflNatural-prop natN prop)
redSubst*Term t⇒u (ne' K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k)) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d'] = [ redFirst*Term t⇒u , ⊢u , t⇒u ⇨∷* d ]
  in  neₜ k [d'] (neNfₜ neK₁ ⊢k k≡k) , neₜ₌ k k [d'] [d] (neNfₜ₌ neK₁ neK₁ k≡k)
redSubst*Term {A} {t} {u} {l} {Γ} t⇒u (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  (Πₜ f [ ⊢t , ⊢u , d ] funcF f≡f [f] [f]₁) =
  let A≡ΠFG = subset* (red D)
      t⇒u'  = conv* t⇒u A≡ΠFG
      [d]  = [ ⊢t , ⊢u , d ]
      [d'] = [ redFirst*Term t⇒u , ⊢u , t⇒u ⇨∷* d ]
      ta×ta≡ua : ∀ {ρ Δ a} ([ρ] : ρ ∷ Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                 ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → (Δ ⊩⟨ l ⟩ U.wk ρ t ∘ a ∷ U.wk (lift ρ) G [ a ] / [G]  [ρ] ⊢Δ [a])
               × (Δ ⊩⟨ l ⟩ U.wk ρ t ∘ a ≡ U.wk ρ u ∘ a ∷
                 U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
      ta×ta≡ua ρ ⊢Δ [a] = let ⊢a = wellformedTerm ([F] ρ ⊢Δ) [a]
                          in  redSubst*Term (app-subst* (wkRed*Term ρ ⊢Δ t⇒u') ⊢a)
                                            ([G] ρ ⊢Δ [a]) ([f]₁ ρ ⊢Δ [a])
      ta : ∀ {ρ Δ a} ([ρ] : ρ ∷ Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
           ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
         → (Δ ⊩⟨ l ⟩ U.wk ρ t ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
      ta ρ ⊢Δ [a] = proj₁ (ta×ta≡ua ρ ⊢Δ [a])
      ta≡ua : ∀ {ρ Δ a} ([ρ] : ρ ∷ Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
            → (Δ ⊩⟨ l ⟩ U.wk ρ t ∘ a ≡ U.wk ρ u ∘ a ∷
              U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
      ta≡ua ρ ⊢Δ [a] = proj₂ (ta×ta≡ua ρ ⊢Δ [a])
      ta≡tb : ∀ {ρ Δ a b} ([ρ] : ρ ∷ Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([b] : Δ ⊩⟨ l ⟩ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([a≡b] : Δ ⊩⟨ l ⟩ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
            → (Δ ⊩⟨ l ⟩ U.wk ρ t ∘ a ≡ U.wk ρ t ∘ b ∷
              U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
      ta≡tb ρ ⊢Δ [a] [b] [a≡b] =
        transEqTerm ([G] ρ ⊢Δ [a]) (ta≡ua ρ ⊢Δ [a])
          (transEqTerm ([G] ρ ⊢Δ [a]) ([f] ρ ⊢Δ [a] [b] [a≡b])
            (convEqTerm₂ ([G] ρ ⊢Δ [a]) ([G] ρ ⊢Δ [b])
                         (G-ext ρ ⊢Δ [a] [b] [a≡b])
                         (symEqTerm ([G] ρ ⊢Δ [b]) (ta≡ua ρ ⊢Δ [b]))))
      t≡t = ≅ₜ-red (id (_⊢_:⇒*:_.⊢A D)) t⇒u t⇒u f≡f
      t≡u = ≅ₜ-red (id (_⊢_:⇒*:_.⊢A D)) t⇒u (id ⊢t) f≡f
  in  Πₜ f [d'] funcF t≡t ta≡tb ta
  ,   Πₜ₌ f f [d'] [d] funcF funcF t≡u
          (Πₜ f [d'] funcF t≡t ta≡tb ta)
          (Πₜ f [d] funcF f≡f [f] [f]₁)
          ta≡ua
redSubst*Term t⇒u (emb 0<1 x) [u] = redSubst*Term t⇒u x [u]

redSubst : ∀ {A B l Γ}
         → Γ ⊢ A ⇒ B
         → Γ ⊩⟨ l ⟩ B
         → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst A⇒B [B] = redSubst* (A⇒B ⇨ id (wellformed [B])) [B]

redSubstTerm : ∀ {A t u l Γ}
             → Γ ⊢ t ⇒ u ∷ A
             → ([A] : Γ ⊩⟨ l ⟩ A)
             → Γ ⊩⟨ l ⟩ u ∷ A / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A / [A]
             × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (t⇒u ⇨ id (wellformedTerm [A] [u])) [A] [u]
