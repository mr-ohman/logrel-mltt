module Definition.LogicalRelation.Irrelevance where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


mutual
  proof-irrelevanceEq : ∀ {Γ A B} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                      → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A ≡ B / q
  proof-irrelevanceEq ⁰ ⁰ (ℕ D) (ℕ D₁) A≡B = A≡B
  proof-irrelevanceEq ⁰ ⁰ (ℕ D) (ne D₁ neK) A≡B = ⊥-elim (ℕ≢ne neK (whrDet*' (red D , ℕ) (red D₁ , (ne neK))))
  proof-irrelevanceEq ⁰ ⁰ (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) A≡B = ⊥-elim (ℕ≢Π (whrDet*' (red D , ℕ) (red D₁ , Π)))

  proof-irrelevanceEq ⁰ ⁰ (ne D neK) (ℕ D₁) A≡B = ⊥-elim (ℕ≢ne neK (whrDet*' (red D₁ , ℕ) (red D , (ne neK))))
  proof-irrelevanceEq ⁰ ⁰ (ne D neK) (ne D₁ neK₁) ne[ M , D' , neM , K≡M ] =
    ne[ M , D' , neM , trans (sym (subset* (red D₁))) (trans (subset* (red D)) K≡M) ]
  proof-irrelevanceEq ⁰ ⁰ (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) A≡B = ⊥-elim (Π≢ne neK (whrDet*' (red D₁ , Π) (red D , (ne neK))))

  proof-irrelevanceEq ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) A≡B = ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (red D , Π)))
  proof-irrelevanceEq ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) A≡B = ⊥-elim (Π≢ne neK (whrDet*' (red D , Π) (red D₁ , (ne neK))))
  proof-irrelevanceEq ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
                          Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
    in Π⁰[ F' , G' , D' , A≡B
         , (λ ρ ⊢Δ → proof-irrelevanceEq' ⁰ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
         , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                          in  proof-irrelevanceEq' ⁰ ⁰ (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]

  proof-irrelevanceEq ⁰ ¹ (ℕ D) U A≡B = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  proof-irrelevanceEq ⁰ ¹ (ℕ D) (ℕ ⊢Γ) A≡B = A≡B
  proof-irrelevanceEq ⁰ ¹ (ℕ D) (Π ⊢F ⊢G q [F] [G] G-ext) A≡B = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))

  proof-irrelevanceEq ⁰ ¹ (ne D neK) U A≡B = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceEq ⁰ ¹ (ne D neK) (ℕ ⊢Γ) A≡B = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceEq ⁰ ¹ (ne D neK) (Π ⊢F ⊢G q [F] [G] G-ext) A≡B = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))

  proof-irrelevanceEq ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U A≡B = ⊥-elim (U≢Π (whnfRed*' (red D) U))
  proof-irrelevanceEq ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ ⊢Γ) A≡B = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
  proof-irrelevanceEq ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁)
                          Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
    in Π¹[ F' , G' , D' , A≡B
       , (λ ρ ⊢Δ → proof-irrelevanceEq' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
       , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                        in  proof-irrelevanceEq' ⁰ ¹ (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) (PE.sym G≡G₁)) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]

  proof-irrelevanceEq ⁰ ¹ p (emb x) A≡B = proof-irrelevanceEq ⁰ ⁰ p x A≡B

  proof-irrelevanceEq ¹ ⁰ U (ℕ D) A≡B = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  proof-irrelevanceEq ¹ ⁰ U (ne D neK) A≡B = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceEq ¹ ⁰ U (Π D ⊢F ⊢G [F] [G] G-ext) A≡B = ⊥-elim (U≢Π (whnfRed*' (red D) U))

  proof-irrelevanceEq ¹ ⁰ (ℕ ⊢Γ) (ℕ D) A≡B = A≡B
  proof-irrelevanceEq ¹ ⁰ (ℕ ⊢Γ) (ne D neK) A≡B = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceEq ¹ ⁰ (ℕ ⊢Γ) (Π D ⊢F ⊢G [F] [G] G-ext) A≡B = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

  proof-irrelevanceEq ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ℕ D) A≡B = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
  proof-irrelevanceEq ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ne D neK) A≡B = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
  proof-irrelevanceEq ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
                          Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
    in Π⁰[ F' , G' , D' , A≡B
         , (λ ρ ⊢Δ → proof-irrelevanceEq' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
         , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                          in proof-irrelevanceEq' ¹ ⁰ (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]

  proof-irrelevanceEq ¹ ⁰ (emb x) q A≡B = proof-irrelevanceEq ⁰ ⁰ x q A≡B

  proof-irrelevanceEq ¹ ¹ U U A≡B = A≡B
  proof-irrelevanceEq ¹ ¹ (ℕ ⊢Γ) (ℕ ⊢Γ₁) A≡B = A≡B
  proof-irrelevanceEq ¹ ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁)
                          Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    Π¹[ F' , G' , D' , A≡B
      , (λ ρ ⊢Δ → proof-irrelevanceEq ¹ ¹ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
      , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm ¹ ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEq ¹ ¹ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]

  proof-irrelevanceEq ¹ ¹ p (emb x) A≡B = proof-irrelevanceEq ¹ ⁰ p x A≡B
  proof-irrelevanceEq ¹ ¹ (emb x) q A≡B = proof-irrelevanceEq ⁰ ¹ x q A≡B

  proof-irrelevanceEq' : ∀ {Γ A A' B} l l' (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A' ≡ B / q
  proof-irrelevanceEq' l l' PE.refl p q A≡B = proof-irrelevanceEq l l' p q A≡B

  proof-irrelevanceEq'' : ∀ {Γ A A' B B'} l l' (eqA : A PE.≡ A') (eqB : B PE.≡ B') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                        → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A' ≡ B' / q
  proof-irrelevanceEq'' l l' PE.refl PE.refl p q A≡B = proof-irrelevanceEq l l' p q A≡B

--------------------------------------------------------------------------------

  proof-irrelevanceTerm : ∀ {Γ A t} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                        → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A / q
  proof-irrelevanceTerm ⁰ ⁰ (ℕ D) (ℕ D₁) t = t
  proof-irrelevanceTerm ⁰ ⁰ (ℕ D) (ne D₁ neK) t = ⊥-elim (ℕ≢ne neK (whrDet*' (red D , ℕ) (red D₁ , (ne neK))))
  proof-irrelevanceTerm ⁰ ⁰ (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) t = ⊥-elim (ℕ≢Π (whrDet*' (red D , ℕ) (red D₁ , Π)))

  proof-irrelevanceTerm ⁰ ⁰ (ne D neK) (ℕ D₁) t = ⊥-elim (ℕ≢ne neK (whrDet*' (red D₁ , ℕ) (red D , (ne neK))))
  proof-irrelevanceTerm ⁰ ⁰ (ne D neK) (ne D₁ neK₁) t = t
  proof-irrelevanceTerm ⁰ ⁰ (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) t = ⊥-elim (Π≢ne neK (whrDet*' (red D₁ , Π) (red D , (ne neK))))

  proof-irrelevanceTerm ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) t = ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (red D , Π)))
  proof-irrelevanceTerm ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) t = ⊥-elim (Π≢ne neK (whrDet*' (red D , Π) (red D₁ , (ne neK))))
  proof-irrelevanceTerm ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
                                   [a]         = proof-irrelevanceTerm' ⁰ ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b]       = proof-irrelevanceEqTerm' ⁰ ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm' ⁰ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))

  proof-irrelevanceTerm ⁰ ¹ (ℕ D) U t = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  proof-irrelevanceTerm ⁰ ¹ (ℕ D) (ℕ ⊢Γ) t = t
  proof-irrelevanceTerm ⁰ ¹ (ℕ D) (Π ⊢F ⊢G q [F] [G] G-ext) t = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))

  proof-irrelevanceTerm ⁰ ¹ (ne D neK) U t = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceTerm ⁰ ¹ (ne D neK) (ℕ ⊢Γ) t = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceTerm ⁰ ¹ (ne D neK) (Π ⊢F ⊢G q [F] [G] G-ext) t = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))

  proof-irrelevanceTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U t = ⊥-elim (U≢Π (whnfRed*' (red D) U))
  proof-irrelevanceTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ ⊢Γ) t = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
  proof-irrelevanceTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
                                   [a]         = proof-irrelevanceTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b]       = proof-irrelevanceEqTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm' ⁰ ¹ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) (PE.sym G≡G₁)) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))

  proof-irrelevanceTerm ⁰ ¹ p (emb x) t = proof-irrelevanceTerm ⁰ ⁰ p x t

  proof-irrelevanceTerm ¹ ⁰ U (ℕ D) t = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  proof-irrelevanceTerm ¹ ⁰ U (ne D neK) t = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceTerm ¹ ⁰ U (Π D ⊢F ⊢G [F] [G] G-ext) t = ⊥-elim (U≢Π (whnfRed*' (red D) U))

  proof-irrelevanceTerm ¹ ⁰ (ℕ ⊢Γ) (ℕ D) t = t
  proof-irrelevanceTerm ¹ ⁰ (ℕ ⊢Γ) (ne D neK) t = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceTerm ¹ ⁰ (ℕ ⊢Γ) (Π D ⊢F ⊢G [F] [G] G-ext) t = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

  proof-irrelevanceTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ℕ D) t = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
  proof-irrelevanceTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ne D neK) t = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
  proof-irrelevanceTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
                                   [a]         = proof-irrelevanceTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b]       = proof-irrelevanceEqTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm' ¹ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))

  proof-irrelevanceTerm ¹ ⁰ (emb x) q t = proof-irrelevanceTerm ⁰ ⁰ x q t

  proof-irrelevanceTerm ¹ ¹ U U t = t
  proof-irrelevanceTerm ¹ ¹ (ℕ ⊢Γ) (ℕ ⊢Γ₁) t = t
  proof-irrelevanceTerm ¹ ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let [a]   = proof-irrelevanceTerm ¹ ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b] = proof-irrelevanceEqTerm ¹ ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm ¹ ¹ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))

  proof-irrelevanceTerm ¹ ¹ (emb x) q t = proof-irrelevanceTerm ⁰ ¹ x q t
  proof-irrelevanceTerm ¹ ¹ p (emb x) t = proof-irrelevanceTerm ¹ ⁰ p x t

  proof-irrelevanceTerm' : ∀ {Γ A A' t} l l' (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A' / q
  proof-irrelevanceTerm' l l' PE.refl p q t = proof-irrelevanceTerm l l' p q t

--------------------------------------------------------------------------------

  proof-irrelevanceEqTerm : ∀ {Γ A t u} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A / q
  proof-irrelevanceEqTerm ⁰ ⁰ (ℕ D) (ℕ D₁) t≡u = t≡u
  proof-irrelevanceEqTerm ⁰ ⁰ (ℕ D) (ne D₁ neK) t≡u = ⊥-elim (ℕ≢ne neK (whrDet*' (red D , ℕ) (red D₁ , (ne neK))))
  proof-irrelevanceEqTerm ⁰ ⁰ (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) t≡u = ⊥-elim (ℕ≢Π (whrDet*' (red D , ℕ) (red D₁ , Π)))

  proof-irrelevanceEqTerm ⁰ ⁰ (ne D neK) (ℕ D₁) t≡u = ⊥-elim (ℕ≢ne neK (whrDet*' (red D₁ , ℕ) (red D , (ne neK))))
  proof-irrelevanceEqTerm ⁰ ⁰ (ne D neK) (ne D₁ neK₁) t≡u = t≡u
  proof-irrelevanceEqTerm ⁰ ⁰ (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) t≡u = ⊥-elim (Π≢ne neK (whrDet*' (red D₁ , Π) (red D , (ne neK))))

  proof-irrelevanceEqTerm ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) t≡u = ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (red D , Π)))
  proof-irrelevanceEqTerm ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) t≡u = ⊥-elim (Π≢ne neK (whrDet*' (red D , Π) (red D₁ , (ne neK))))
  proof-irrelevanceEqTerm ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
        [A]         = Π D ⊢F ⊢G [F] [G] G-ext
        [A]₁        = Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm ⁰ ⁰ [A] [A]₁ ⊩t , proof-irrelevanceTerm ⁰ ⁰ [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm' ⁰ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))

  proof-irrelevanceEqTerm ⁰ ¹ (ℕ D) U t≡u = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  proof-irrelevanceEqTerm ⁰ ¹ (ℕ D) (ℕ ⊢Γ) t≡u = t≡u
  proof-irrelevanceEqTerm ⁰ ¹ (ℕ D) (Π ⊢F ⊢G q [F] [G] G-ext) t≡u = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))

  proof-irrelevanceEqTerm ⁰ ¹ (ne D neK) U t≡u = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceEqTerm ⁰ ¹ (ne D neK) (ℕ ⊢Γ) t≡u = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceEqTerm ⁰ ¹ (ne D neK) (Π ⊢F ⊢G q [F] [G] G-ext) t≡u = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))

  proof-irrelevanceEqTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U t≡u = ⊥-elim (U≢Π (whnfRed*' (red D) U))
  proof-irrelevanceEqTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ ⊢Γ) t≡u = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
  proof-irrelevanceEqTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity ((whnfRed*' (red D) Π))
        [A]         = Π D ⊢F ⊢G [F] [G] G-ext
        [A]₁        = Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm ⁰ ¹ [A] [A]₁ ⊩t , proof-irrelevanceTerm ⁰ ¹ [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm' ⁰ ¹ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) (PE.sym G≡G₁)) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))

  proof-irrelevanceEqTerm ⁰ ¹ p (emb x) t≡u = proof-irrelevanceEqTerm ⁰ ⁰ p x t≡u

  proof-irrelevanceEqTerm ¹ ⁰ U (ℕ D) t≡u = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  proof-irrelevanceEqTerm ¹ ⁰ U (ne D neK) t≡u = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceEqTerm ¹ ⁰ U (Π D ⊢F ⊢G [F] [G] G-ext) t≡u = ⊥-elim (U≢Π (whnfRed*' (red D) U))

  proof-irrelevanceEqTerm ¹ ⁰ (ℕ ⊢Γ) (ℕ D) t≡u = t≡u
  proof-irrelevanceEqTerm ¹ ⁰ (ℕ ⊢Γ) (ne D neK) t≡u = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceEqTerm ¹ ⁰ (ℕ ⊢Γ) (Π D ⊢F ⊢G [F] [G] G-ext) t≡u = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

  proof-irrelevanceEqTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ℕ D) t≡u = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
  proof-irrelevanceEqTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ne D neK) t≡u = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
  proof-irrelevanceEqTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity ((whnfRed*' (red D) Π))
        [A]         = Π ⊢F ⊢G p [F] [G] G-ext
        [A]₁        = Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm ¹ ⁰ [A] [A]₁ ⊩t , proof-irrelevanceTerm ¹ ⁰ [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm' ¹ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))

  proof-irrelevanceEqTerm ¹ ⁰ (emb x) q t≡u = proof-irrelevanceEqTerm ⁰ ⁰ x q t≡u

  proof-irrelevanceEqTerm ¹ ¹ U U t≡u = t≡u
  proof-irrelevanceEqTerm ¹ ¹ (ℕ ⊢Γ) (ℕ ⊢Γ₁) t≡u = t≡u
  proof-irrelevanceEqTerm ¹ ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let [A]         = Π ⊢F ⊢G p [F] [G] G-ext
        [A]₁        = Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm ¹ ¹ [A] [A]₁ ⊩t , proof-irrelevanceTerm ¹ ¹ [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm ¹ ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm ¹ ¹ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))

  proof-irrelevanceEqTerm ¹ ¹ (emb x) q t≡u = proof-irrelevanceEqTerm ⁰ ¹ x q t≡u
  proof-irrelevanceEqTerm ¹ ¹ p (emb x) t≡u = proof-irrelevanceEqTerm ¹ ⁰ p x t≡u

  proof-irrelevanceEqTerm' : ∀ {Γ A A' t u} l l' (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A' / q
  proof-irrelevanceEqTerm' l l' PE.refl p q t≡u = proof-irrelevanceEqTerm l l' p q t≡u

  proof-irrelevanceEqTerm'' : ∀ {Γ A A' t t' u u'} l l' (eqt : t PE.≡ t') (equ : u PE.≡ u') (eqA : A PE.≡ A')
                              (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t' ≡ u' ∷ A' / q
  proof-irrelevanceEqTerm'' l l' PE.refl PE.refl PE.refl p q t≡u = proof-irrelevanceEqTerm l l' p q t≡u
