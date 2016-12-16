open import Definition.EqualityRelation

module Definition.LogicalRelation.Properties.Reduction {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
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
redSubst*Term t⇒u (U' .⁰ 0<1 ⊢Γ) (Uₜ ⊢u u≡u ⊩u) =
  let ⊢t = redFirst*Term t⇒u
      q = redSubst* (univ* t⇒u) (univEq (U' ⁰ 0<1 ⊢Γ) (Uₜ ⊢u u≡u ⊩u))
  in  Uₜ ⊢t (≅ₜ-red (id (U ⊢Γ)) t⇒u t⇒u u≡u) (proj₁ q)
  ,   Uₜ₌ ⊢t ⊢u (≅ₜ-red (id (U ⊢Γ)) t⇒u (id ⊢u) u≡u)
          (proj₁ q) ⊩u (proj₂ q)
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
              (Πₜ proj₁' t≡t proj₂' proj₃') =
  let A≡ΠFG = subset* (red D)
      ⊢t    = redFirst*Term t⇒u
      t⇒u'  = conv* t⇒u A≡ΠFG
      ta×ta≡ua : ∀ {Δ a} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                 ([a] : Δ ⊩⟨ l ⟩ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
               → (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
               × (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷
                 wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
      ta×ta≡ua ρ ⊢Δ [a] = let ⊢a = wellformedTerm ([F] ρ ⊢Δ) [a]
                          in  redSubst*Term (app-subst* (wkRed*Term ρ ⊢Δ t⇒u') ⊢a)
                                            ([G] ρ ⊢Δ [a]) (proj₃' ρ ⊢Δ [a])
      ta : ∀ {Δ a} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
           ([a] : Δ ⊩⟨ l ⟩ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
         → (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
      ta ρ ⊢Δ [a] = proj₁ (ta×ta≡ua ρ ⊢Δ [a])
      ta≡ua : ∀ {Δ a} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩⟨ l ⟩ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
            → (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷
              wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
      ta≡ua ρ ⊢Δ [a] = proj₂ (ta×ta≡ua ρ ⊢Δ [a])
      ta≡tb : ∀ {Δ a b} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩⟨ l ⟩ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
              ([b] : Δ ⊩⟨ l ⟩ b ∷ wkₜ ρ F / [F] ρ ⊢Δ)
              ([a≡b] : Δ ⊩⟨ l ⟩ a ≡ b ∷ wkₜ ρ F / [F] ρ ⊢Δ)
            → (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ≡ wkₜ ρ t ∘ b ∷
              wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
      ta≡tb ρ ⊢Δ [a] [b] [a≡b] =
        transEqTerm ([G] ρ ⊢Δ [a]) (ta≡ua ρ ⊢Δ [a])
          (transEqTerm ([G] ρ ⊢Δ [a]) (proj₂' ρ ⊢Δ [a] [b] [a≡b])
            (convEqTerm₂ ([G] ρ ⊢Δ [a]) ([G] ρ ⊢Δ [b])
                         (G-ext ρ ⊢Δ [a] [b] [a≡b])
                         (symEqTerm ([G] ρ ⊢Δ [b]) (ta≡ua ρ ⊢Δ [b]))))
  in  Πₜ ⊢t (≅ₜ-red (id (_⊢_:⇒*:_.⊢A D)) t⇒u t⇒u t≡t) ta≡tb ta
  ,   Πₜ₌ (≅ₜ-red (id (_⊢_:⇒*:_.⊢A D)) t⇒u (id proj₁') t≡t)
          (Πₜ ⊢t (≅ₜ-red (id (_⊢_:⇒*:_.⊢A D)) t⇒u t⇒u t≡t) ta≡tb ta)
          (Πₜ proj₁' t≡t proj₂' proj₃')
          ta≡ua
  --,   subset*Term t⇒u , (⊢t , ta≡tb , ta) , (proj₁' , proj₂' , proj₃') , ta≡ua
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
