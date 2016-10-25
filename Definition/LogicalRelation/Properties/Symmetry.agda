module Definition.LogicalRelation.Properties.Symmetry where

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


mutual
  symEqT : ∀ {Γ A B l l'} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
         → Tactic Γ l l' A B [A] [B]
         → Γ ⊩⟨ l  ⟩ A ≡ B / [A]
         → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symEqT (ℕ (ℕ D) (ℕ D₁)) A≡B = red D
  symEqT (ne (ne K D neK) (ne K₁ D₁ neK₁)) ne[ M , D' , neM , K≡M ] =
    ne[ _ , D , neK
      , trans (sym (subset* (red D₁))) (trans (subset* (red D')) (sym K≡M)) ]
  symEqT (Π (Π F G D ⊢F ⊢G [F] [G] G-ext) (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁))
         Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
        [F₁≡F] : ∀ {Δ} ρ ⊢Δ → _
        [F₁≡F] {Δ} ρ ⊢Δ =
          let ρF'≡ρF₁ ρ = PE.cong (U.wk ρ) (PE.sym F₁≡F')
              [ρF'] ρ ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)
          in  irrelevanceEq' {Δ} (ρF'≡ρF₁ (toWk ρ))
                             ([ρF'] ρ ⊢Δ) ([F]₁ ρ ⊢Δ)
                             (symEq ([F] ρ ⊢Δ) ([ρF'] ρ ⊢Δ)
                                    ([F≡F'] ρ ⊢Δ))
    in  Π¹[ _ , _ , red D , sym A≡B
          , [F₁≡F]
          , (λ ρ ⊢Δ [a] →
               let ρG'a≡ρG₁'a = PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')
                   [ρG'a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ wkLiftₜ ρ x [ _ ]) G₁≡G'
                                     ([G]₁ ρ ⊢Δ [a])
                   [a]₁ = convTerm₁ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) ([F₁≡F] ρ ⊢Δ) [a]
               in  irrelevanceEq' ρG'a≡ρG₁'a
                                  [ρG'a]
                                  ([G]₁ ρ ⊢Δ [a])
                                  (symEq ([G] ρ ⊢Δ [a]₁) [ρG'a]
                                         ([G≡G'] ρ ⊢Δ [a]₁))) ]
  symEqT (U UA UB) A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  symEq : ∀ {Γ A B l l'} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
        → Γ ⊩⟨ l ⟩ A ≡ B / [A]
        → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

symNatural-prop : ∀ {Γ k k'} ([k≡k'] : [Natural] k k')
                → [Natural]-prop Γ k k' [k≡k']
                → [Natural]-prop Γ k' k (symNatural [k≡k'])
symNatural-prop suc ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ] =
  ℕ≡[ k' , k , d' , d , sym t≡u
    , symNatural [k≡k'] , symNatural-prop [k≡k'] prop ]
symNatural-prop zero prop = prop
symNatural-prop (ne x x₁) prop = sym prop

symEqTerm : ∀ {l Γ A t u} ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
          → Γ ⊩⟨ l ⟩ u ≡ t ∷ A / [A]
symEqTerm (U (U .⁰ 0<1 ⊢Γ)) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] =
  U[ ⊢u , ⊢t , sym t≡u , ⊩u , ⊩t , symEq ⊩t ⊩u [t≡u] ]
symEqTerm (ℕ ℕA) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ] =
  ℕ≡[ k' , k , d' , d , sym t≡u
    , symNatural [k≡k'] , symNatural-prop [k≡k'] prop ]
symEqTerm (ne (ne K D neK)) t≡u = sym t≡u
symEqTerm (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (t≡u , ⊩t , ⊩u , [t≡u]) =
  sym t≡u , ⊩u , ⊩t , (λ ρ ⊢Δ [a] → symEqTerm ([G] ρ ⊢Δ [a]) ([t≡u] ρ ⊢Δ [a]))
symEqTerm (emb {l< = 0<1} x) t≡u = symEqTerm x t≡u
