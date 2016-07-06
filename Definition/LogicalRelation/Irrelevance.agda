module Definition.LogicalRelation.Irrelevance where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


mutual
  proof-irrelevanceEq : ∀ {Γ A B l l'} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A ≡ B / q
  proof-irrelevanceEq p q A≡B = proof-irrelevanceEqT (goodCasesRefl p q) A≡B

  proof-irrelevanceEq' : ∀ {Γ A A' B l l'} (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A' ≡ B / q
  proof-irrelevanceEq' PE.refl p q A≡B = proof-irrelevanceEq p q A≡B

  proof-irrelevanceEq'' : ∀ {Γ A A' B B' l l'} (eqA : A PE.≡ A') (eqB : B PE.≡ B') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                        → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A' ≡ B' / q
  proof-irrelevanceEq'' PE.refl PE.refl p q A≡B = proof-irrelevanceEq p q A≡B

  proof-irrelevanceEqT : ∀ {Γ A B l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                       → Tactic Γ l l' A A p q
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A ≡ B / q
  proof-irrelevanceEqT (ℕ D D₁) A≡B = A≡B
  proof-irrelevanceEqT (ne D neK D₁ neK₁) ne[ M , D' , neM , K≡M ] = ne[ M , D' , neM , (trans (sym (subset* (red D₁))) (trans (subset* (red D)) K≡M)) ]
  proof-irrelevanceEqT (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
    in  Π¹[ F' , G' , D' , A≡B
          , (λ ρ ⊢Δ → proof-irrelevanceEq' (PE.cong (wkₜ ρ) F≡F₁) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
          , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                           in  proof-irrelevanceEq' (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]
  proof-irrelevanceEqT (U ⊢Γ ⊢Γ₁) A≡B = A≡B
  proof-irrelevanceEqT (emb⁰¹ x) A≡B = proof-irrelevanceEqT x A≡B
  proof-irrelevanceEqT (emb¹⁰ x) A≡B = proof-irrelevanceEqT x A≡B

--------------------------------------------------------------------------------

  proof-irrelevanceTerm : ∀ {Γ A t l l'} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                        → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A / q
  proof-irrelevanceTerm p q t = proof-irrelevanceTermT (goodCasesRefl p q) t

  proof-irrelevanceTerm' : ∀ {Γ A A' t l l'} (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A' / q
  proof-irrelevanceTerm' PE.refl p q t = proof-irrelevanceTerm p q t

  proof-irrelevanceTerm'' : ∀ {Γ A A' t t' l l'}
                            (eqA : A PE.≡ A') (eqt : t PE.≡ t')
                            (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                          → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t' ∷ A' / q
  proof-irrelevanceTerm'' PE.refl PE.refl p q t = proof-irrelevanceTerm p q t

  proof-irrelevanceTermT : ∀ {Γ A t l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                         → Tactic Γ l l' A A p q
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A / q
  proof-irrelevanceTermT (ℕ D D₁) t = t
  proof-irrelevanceTermT (ne D neK D₁ neK₁) t = t
  proof-irrelevanceTermT (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [b]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
                                        [a]         = proof-irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                        [b]         = proof-irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [b]₁
                                        [a≡b]       = proof-irrelevanceEqTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                                    in  proof-irrelevanceEqTerm' (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [b] [a≡b]))
  proof-irrelevanceTermT (U ⊢Γ ⊢Γ₁) t = t
  proof-irrelevanceTermT (emb⁰¹ x) t = proof-irrelevanceTermT x t
  proof-irrelevanceTermT (emb¹⁰ x) t = proof-irrelevanceTermT x t

--------------------------------------------------------------------------------

  proof-irrelevanceEqTerm : ∀ {Γ A t u l l'} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A / q
  proof-irrelevanceEqTerm p q t≡u = proof-irrelevanceEqTermT (goodCasesRefl p q) t≡u

  proof-irrelevanceEqTerm' : ∀ {Γ A A' t u l l'} (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A' / q
  proof-irrelevanceEqTerm' PE.refl p q t≡u = proof-irrelevanceEqTerm p q t≡u

  proof-irrelevanceEqTerm'' : ∀ {Γ A A' t t' u u' l l'} (eqt : t PE.≡ t') (equ : u PE.≡ u') (eqA : A PE.≡ A')
                              (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t' ≡ u' ∷ A' / q
  proof-irrelevanceEqTerm'' PE.refl PE.refl PE.refl p q t≡u = proof-irrelevanceEqTerm p q t≡u

  proof-irrelevanceEqTermT : ∀ {Γ A t u} {l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                           → Tactic Γ l l' A A p q
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A / q
  proof-irrelevanceEqTermT (ℕ D D₁) t≡u = t≡u
  proof-irrelevanceEqTermT (ne D neK D₁ neK₁) t≡u = t≡u
  proof-irrelevanceEqTermT (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
        [A]         = Π D ⊢F ⊢G [F] [G] G-ext
        [A]₁        = Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm [A] [A]₁ ⊩t , proof-irrelevanceTerm [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm' (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))
  proof-irrelevanceEqTermT (U ⊢Γ ⊢Γ₁) t≡u = t≡u
  proof-irrelevanceEqTermT (emb⁰¹ x) t≡u = proof-irrelevanceEqTermT x t≡u
  proof-irrelevanceEqTermT (emb¹⁰ x) t≡u = proof-irrelevanceEqTermT x t≡u
