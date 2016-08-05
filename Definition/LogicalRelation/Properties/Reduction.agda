module Definition.LogicalRelation.Properties.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Symmetry
open import Definition.LogicalRelation.Properties.Transitivity
open import Definition.LogicalRelation.Properties.Conversion
open import Definition.LogicalRelation.Properties.Univalence
open import Definition.LogicalRelation.Properties.Soundness

open import Tools.Context

open import Data.Product
open import Data.Empty

import Relation.Binary.PropositionalEquality as PE


redSubst : ∀ {A B l Γ}
         → Γ ⊢ A
         → Γ ⊢ A ⇒ B
         → Γ ⊩⟨ l ⟩ B
         → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst ⊢A A⇒B (U {l< = 0<1} ⊢Γ) = ⊥-elim (redU A⇒B)
redSubst ⊢A A⇒B (ℕ [ ⊢B , ⊢ℕ , D ]) = ℕ ([ ⊢A , ⊢ℕ , A⇒B ⇨ D ]) , D
redSubst ⊢A A⇒B (ne [ ⊢B , ⊢K , D ] neK) =
  ne [ ⊢A , ⊢K , A⇒B ⇨ D ] neK
  , ne[ _ , [ ⊢B , ⊢K , D ] , neK , refl ⊢K ]
redSubst ⊢A A⇒B (Π [ ⊢B , ⊢ΠFG , D ] ⊢F ⊢G [F] [G] G-ext) =
  Π [ ⊢A , ⊢ΠFG , A⇒B ⇨ D ] ⊢F ⊢G [F] [G] G-ext
  , Π¹[ _ , _ , D , subset A⇒B , (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])) ]
redSubst ⊢A A⇒B (emb {l< = 0<1} x) =
  let y , y₁ = redSubst ⊢A A⇒B x
  in emb {l< = 0<1} y , y₁

redSubstTerm : ∀ {A t u l Γ}
             → Γ ⊢ t ∷ A
             → Γ ⊢ t ⇒ u ∷ A
             → ([A] : Γ ⊩⟨ l ⟩ A)
             → Γ ⊩⟨ l ⟩ u ∷ A / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A / [A]
             × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubstTerm ⊢t t⇒u (U {l< = 0<1} ⊢Γ) [u] =
  let q = redSubst (univ ⊢t) (univ t⇒u) (univEq (U {l< = 0<1} ⊢Γ) [u])
  in  (⊢t , proj₁ q) , U[ ⊢t , proj₁ [u] , subsetTerm t⇒u , proj₁ q , proj₂ [u] , proj₂ q ]
redSubstTerm ⊢t t⇒u (ℕ D) ℕ[ n , [ ⊢u , ⊢n , d ] , natN , prop ] =
  let A≡ℕ = subset* (red D)
      ⊢t'  = conv ⊢t A≡ℕ
      t⇒u' = conv t⇒u A≡ℕ
  in  ℕ[ n , [ ⊢t' , ⊢n , t⇒u' ⇨ d ] , natN , prop ]
  ,   ℕ≡[ n , n , [ ⊢t' , ⊢n , t⇒u' ⇨ d ] , [ ⊢u , ⊢n , d ] , subsetTerm t⇒u' , reflNatural natN prop ]
redSubstTerm ⊢t t⇒u (ne D neK) [u] = ⊢t , subsetTerm t⇒u
redSubstTerm {A} {t} {u} {l} {Γ} ⊢t t⇒u (Π {F} {G} D ⊢F ⊢G [F] [G] G-ext) (proj₁' , proj₂' , proj₃') =
  let A≡ΠFG = subset* (red D)
      ⊢t'   = conv ⊢t A≡ΠFG
      t⇒u'  = conv t⇒u A≡ΠFG
      ta×ta≡ua : ∀ {Δ a} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                 ([a] : Δ ⊩⟨ l ⟩ a ∷ wkₜ ρ F / [F] ρ ⊢Δ)
               → (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ∷ wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
               × (Δ ⊩⟨ l ⟩ wkₜ ρ t ∘ a ≡ wkₜ ρ u ∘ a ∷
                 wkLiftₜ ρ G [ a ] / [G] ρ ⊢Δ [a])
      ta×ta≡ua ρ ⊢Δ [a] = let ⊢a = soundnessTerm ([F] ρ ⊢Δ) [a]
                          in  redSubstTerm (wkTerm ρ ⊢Δ ⊢t' ∘ ⊢a)
                                           (app-subst (wkRedTerm ρ ⊢Δ t⇒u') ⊢a)
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
  ,   subsetTerm t⇒u , (⊢t , ta≡tb , ta) , (proj₁' , proj₂' , proj₃') , ta≡ua
redSubstTerm ⊢t t⇒u (emb {l< = 0<1} x) [u] = redSubstTerm ⊢t t⇒u x [u]
