module Definition.LogicalRelation.Properties.Reduction where

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
open import Definition.LogicalRelation.Properties.Soundness

open import Data.Product
open import Data.Empty

import Relation.Binary.PropositionalEquality as PE


redSubst* : ∀ {A B l Γ}
          → Γ ⊢ A ⇒* B
          → Γ ⊩⟨ l ⟩ B
          → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst* D (U (U l' l< ⊢Γ)) rewrite redU* D =
  U (U l' l< ⊢Γ) , PE.refl
redSubst* D (ℕ (ℕ [ ⊢B , ⊢ℕ , D' ])) =
  let ⊢A = redFirst* D
  in  ℕ (ℕ ([ ⊢A , ⊢ℕ , D ⇨* D' ])) , D'
redSubst* D (ne (ne K [ ⊢B , ⊢K , D' ] neK)) =
  let ⊢A = redFirst* D
  in  ne (ne K [ ⊢A , ⊢K , D ⇨* D' ] neK)
  ,   ne[ _ , [ ⊢B , ⊢K , D' ] , neK , refl ⊢K ]
redSubst* D (Π (Π F G [ ⊢B , ⊢ΠFG , D' ] ⊢F ⊢G [F] [G] G-ext)) =
  let ⊢A = redFirst* D
  in  Π (Π F G [ ⊢A , ⊢ΠFG , D ⇨* D' ] ⊢F ⊢G [F] [G] G-ext)
  ,   Π¹[ _ , _ , D' , subset* D , (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])) ]
redSubst* D (emb {l< = 0<1} x) with redSubst* D x
redSubst* D (emb {l< = 0<1} x) | y , y₁ = emb {l< = 0<1} y , y₁

redSubst*Term : ∀ {A t u l Γ}
              → Γ ⊢ t ⇒* u ∷ A
              → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ u ∷ A / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubst*Term t⇒u (U (U .⁰ 0<1 ⊢Γ)) [u] =
  let ⊢t = redFirst*Term t⇒u
      q = redSubst* (univ* t⇒u) (univEq (U (U ⁰ 0<1 ⊢Γ)) [u])
  in  (⊢t , proj₁ q) , U[ ⊢t , proj₁ [u] , subset*Term t⇒u , proj₁ q , proj₂ [u] , proj₂ q ]
redSubst*Term t⇒u (ℕ (ℕ D)) ℕ[ n , [ ⊢u , ⊢n , d ] , natN , prop ] =
  let A≡ℕ  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡ℕ
      t⇒u' = conv* t⇒u A≡ℕ
  in  ℕ[ n , [ ⊢t , ⊢n , t⇒u' ⇨∷* d ] , natN , prop ]
  ,   ℕ≡[ n , n , [ ⊢t , ⊢n , t⇒u' ⇨∷* d ] , [ ⊢u , ⊢n , d ] , subset*Term t⇒u' , reflNatural natN , reflNatural-prop natN prop ]
redSubst*Term t⇒u (ne (ne K D neK)) [u] = redFirst*Term t⇒u , subset*Term t⇒u
redSubst*Term {A} {t} {u} {l} {Γ} t⇒u (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (proj₁' , proj₂' , proj₃') =
  let A≡ΠFG = subset* (red D)
      ⊢t    = redFirst*Term t⇒u
      t⇒u'  = conv* t⇒u A≡ΠFG
      ta×ta≡ua : ∀ {Δ a} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                 ([a] : Δ ⊩⟨ l ⟩ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
               → (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
               × (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷
                 wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
      ta×ta≡ua ρ ⊢Δ [a] = let ⊢a = soundnessTerm ([F] ρ ⊢Δ) [a]
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
  in  (⊢t , ta≡tb , ta)
  ,   subset*Term t⇒u , (⊢t , ta≡tb , ta) , (proj₁' , proj₂' , proj₃') , ta≡ua
redSubst*Term t⇒u (emb {l< = 0<1} x) [u] = redSubst*Term t⇒u x [u]

redSubst : ∀ {A B l Γ}
         → Γ ⊢ A ⇒ B
         → Γ ⊩⟨ l ⟩ B
         → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst A⇒B [B] = redSubst* (A⇒B ⇨ id (soundness [B])) [B]

redSubstTerm : ∀ {A t u l Γ}
             → Γ ⊢ t ⇒ u ∷ A
             → ([A] : Γ ⊩⟨ l ⟩ A)
             → Γ ⊩⟨ l ⟩ u ∷ A / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A / [A]
             × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (t⇒u ⇨ id (soundnessTerm [A] [u])) [A] [u]
