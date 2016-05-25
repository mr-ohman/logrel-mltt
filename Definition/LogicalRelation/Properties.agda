module Definition.LogicalRelation.Properties where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation

open import Tools.Context

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


reflEq : ∀ {Γ A} l ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq ⁰ (ℕ [ ⊢A , ⊢B , D ]) = D
reflEq ⁰ (ne [ ⊢A , ⊢B , D ] neK) = ne[ _ , [ ⊢A , ⊢B , D ] , neK , (refl ⊢B) ]
reflEq ⁰ (Π {F} {G} [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) =
  Π⁰[ F , G , D , refl ⊢A , (λ ρ ⊢Δ → reflEq ⁰ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ⁰ ([G] ρ ⊢Δ [a])) ]
reflEq ¹ U = PE.refl
reflEq ¹ ℕ = {!PE.refl!}
reflEq ¹ (Π ⊢F ⊢G ⊩F [F] [G] G-ext) = Π¹[ _ , _ , {!PE.refl!} , {!PE.refl!} , (λ ρ ⊢Δ → reflEq ¹ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ¹ ([G] ρ ⊢Δ [a])) ]
reflEq ¹ (emb x) = reflEq ⁰ x

symEq : ∀ {Γ A B} l ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l ⟩ B) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l ⟩ B ≡ A / [B]
symEq ⁰ (ℕ x) (ℕ x₁) A≡B = red x
symEq ⁰ (ℕ D) (ne D₁ neK) A≡B = ⊥-elim (ℕ≢ne neK (whrDet*' (A≡B , ℕ) (red D₁ , (ne neK))))
symEq ⁰ (ℕ x) (Π x₁ x₂ x₃ [F] [G] x₄) A≡B = ⊥-elim (ℕ≢Π (whrDet*' (A≡B , ℕ) (red x₁ , Π)))

symEq ⁰ (ne x neK) (ℕ D) ne[ M , D' , neM , K≡M ] = ⊥-elim (ℕ≢ne neM (whrDet*' (red D , ℕ) (red D' , ne neM)))
symEq ⁰ (ne D neK) (ne D₁ neK₁) ne[ M , D' , neM , K≡M ] = ne[ _ , D , neK , trans (sym (subset* (red D₁))) (trans (subset* (red D')) (sym K≡M)) ]
symEq ⁰ (ne x neK) (Π D ⊢F ⊢G [F] [G] G-ext) ne[ M , D' , neM , K≡M ] = ⊥-elim (Π≢ne neM (whrDet*' (red D , Π) (red D' , (ne neM))))

symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (D' , Π)))
symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (Π≢ne neK (whrDet*' (D' , Π) (red D₁ , (ne neK))))
symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  Π⁰[ _ , _ , red D , sym A≡B , (λ ρ ⊢Δ → {![F≡F']!}) , {!!} ]

symEq ¹ U U A≡B = PE.refl
symEq ¹ U ℕ A≡B = {!!}
symEq ¹ U (Π ⊢F ⊢G [B] [F] [G] G-ext) A≡B = {!!}
symEq ¹ U (emb x) A≡B = {!!}

symEq ¹ ℕ [B] A≡B = {!!}
symEq ¹ (Π ⊢F ⊢G [A] [F] [G] G-ext) [B] A≡B = {!!}
symEq ¹ (emb x) [B] A≡B = {!!}


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
  proof-irrelevanceEq ⁰ ¹ (ℕ D) ℕ A≡B = A≡B
  proof-irrelevanceEq ⁰ ¹ (ℕ D) (Π ⊢F ⊢G q [F] [G] G-ext) A≡B = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))

  proof-irrelevanceEq ⁰ ¹ (ne D neK) U A≡B = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceEq ⁰ ¹ (ne D neK) ℕ A≡B = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceEq ⁰ ¹ (ne D neK) (Π ⊢F ⊢G q [F] [G] G-ext) A≡B = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))

  proof-irrelevanceEq ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U A≡B = ⊥-elim (U≢Π (whnfRed*' (red D) U))
  proof-irrelevanceEq ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) ℕ A≡B = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
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

  proof-irrelevanceEq ¹ ⁰ ℕ (ℕ D) A≡B = A≡B
  proof-irrelevanceEq ¹ ⁰ ℕ (ne D neK) A≡B = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceEq ¹ ⁰ ℕ (Π D ⊢F ⊢G [F] [G] G-ext) A≡B = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

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
  proof-irrelevanceEq ¹ ¹ ℕ ℕ A≡B = A≡B
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
  proof-irrelevanceTerm ⁰ ¹ (ℕ D) ℕ t = t
  proof-irrelevanceTerm ⁰ ¹ (ℕ D) (Π ⊢F ⊢G q [F] [G] G-ext) t = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))

  proof-irrelevanceTerm ⁰ ¹ (ne D neK) U t = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceTerm ⁰ ¹ (ne D neK) ℕ t = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceTerm ⁰ ¹ (ne D neK) (Π ⊢F ⊢G q [F] [G] G-ext) t = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))

  proof-irrelevanceTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U t = ⊥-elim (U≢Π (whnfRed*' (red D) U))
  proof-irrelevanceTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) ℕ t = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
  proof-irrelevanceTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
                                   [a]         = proof-irrelevanceTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b]       = proof-irrelevanceEqTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm' ⁰ ¹ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) (PE.sym G≡G₁)) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))

  proof-irrelevanceTerm ⁰ ¹ p (emb x) t = proof-irrelevanceTerm ⁰ ⁰ p x t

  proof-irrelevanceTerm ¹ ⁰ U (ℕ D) t = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  proof-irrelevanceTerm ¹ ⁰ U (ne D neK) t = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceTerm ¹ ⁰ U (Π D ⊢F ⊢G [F] [G] G-ext) t = ⊥-elim (U≢Π (whnfRed*' (red D) U))

  proof-irrelevanceTerm ¹ ⁰ ℕ (ℕ D) t = t
  proof-irrelevanceTerm ¹ ⁰ ℕ (ne D neK) t = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceTerm ¹ ⁰ ℕ (Π D ⊢F ⊢G [F] [G] G-ext) t = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

  proof-irrelevanceTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ℕ D) t = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
  proof-irrelevanceTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (ne D neK) t = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
  proof-irrelevanceTerm ¹ ⁰ (Π ⊢F ⊢G p [F] [G] G-ext) (Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
                                   [a]         = proof-irrelevanceTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b]       = proof-irrelevanceEqTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm' ¹ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))

  proof-irrelevanceTerm ¹ ⁰ (emb x) q t = proof-irrelevanceTerm ⁰ ⁰ x q t

  proof-irrelevanceTerm ¹ ¹ U U t = t
  proof-irrelevanceTerm ¹ ¹ ℕ ℕ t = t
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
  proof-irrelevanceEqTerm ⁰ ¹ (ℕ D) ℕ t≡u = t≡u
  proof-irrelevanceEqTerm ⁰ ¹ (ℕ D) (Π ⊢F ⊢G q [F] [G] G-ext) t≡u = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))

  proof-irrelevanceEqTerm ⁰ ¹ (ne D neK) U t≡u = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  proof-irrelevanceEqTerm ⁰ ¹ (ne D neK) ℕ t≡u = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceEqTerm ⁰ ¹ (ne D neK) (Π ⊢F ⊢G q [F] [G] G-ext) t≡u = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))

  proof-irrelevanceEqTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U t≡u = ⊥-elim (U≢Π (whnfRed*' (red D) U))
  proof-irrelevanceEqTerm ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) ℕ t≡u = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
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

  proof-irrelevanceEqTerm ¹ ⁰ ℕ (ℕ D) t≡u = t≡u
  proof-irrelevanceEqTerm ¹ ⁰ ℕ (ne D neK) t≡u = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  proof-irrelevanceEqTerm ¹ ⁰ ℕ (Π D ⊢F ⊢G [F] [G] G-ext) t≡u = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

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
  proof-irrelevanceEqTerm ¹ ¹ ℕ ℕ t≡u = t≡u
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


mutual
  wk : ∀ {Γ Δ A} l → (ρ : Γ ⊆ Δ) → ⊢ Δ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ U.wkₜ ρ A
  wk ⁰ ρ ⊢Δ (ℕ x) = ℕ (T.wkRed:*: ρ ⊢Δ x)
  wk ⁰ ρ ⊢Δ (ne x x₁) = ne (T.wkRed:*: ρ ⊢Δ x) (wkNeutral (toWk ρ) x₁)
  wk ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] x₃) =
    let y = T.wk ρ ⊢Δ x₁
    in Π (T.wkRed:*: ρ ⊢Δ x) y (T.wk (lift ρ) (⊢Δ ∙ y) x₂)
         (λ ρ₁ ⊢Δ₁ → wk ⁰ ρ₁ ⊢Δ₁ ([F] ρ ⊢Δ)) (λ ρ₁ ⊢Δ₁ x₄ → {![G]!}) {!!}
  wk ¹ ρ ⊢Δ U = U
  wk ¹ ρ ⊢Δ ℕ = ℕ
  wk ¹ ρ ⊢Δ (Π F G A [F] [G] G-ext) = let y = T.wk ρ ⊢Δ F in Π y (T.wk (lift ρ) (⊢Δ ∙ y) G) ([F] ρ ⊢Δ) (λ ρ₁ ⊢Δ₁ → wk ¹ ρ₁ ⊢Δ₁ ([F] ρ ⊢Δ)) {!!} {!!}
  wk ¹ ρ ⊢Δ (emb x) = emb (wk ⁰ ρ ⊢Δ x)

  wkEq : ∀ {Γ Δ A B} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A]
       → Δ ⊩⟨ l ⟩ U.wkₜ ρ A ≡ U.wkₜ ρ B / wk l ρ ⊢Δ [A]
  wkEq ⁰ ρ ⊢Δ (ℕ x) A≡B = T.wkRed* ρ ⊢Δ A≡B
  wkEq ⁰ ρ ⊢Δ (ne x x₁) ne[ M , D' , neM , K≡M ] = ne[ wkₜ ρ M , T.wkRed:*: ρ ⊢Δ D' , wkNeutral (toWk ρ) neM , T.wkEq ρ ⊢Δ K≡M ]
  wkEq ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    Π⁰[ wkₜ ρ F' , wkLiftₜ ρ G' , T.wkRed* ρ ⊢Δ D' , T.wkEq ρ ⊢Δ A≡B , {!!} , {!!} ]
  wkEq ¹ ρ ⊢Δ U A≡B = PE.cong (wkₜ ρ) A≡B
  wkEq ¹ ρ ⊢Δ ℕ A≡B = {!PE.cong (wkₜ ρ) A≡B!}
  wkEq ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    Π¹[ wkₜ ρ F' , wkLiftₜ ρ G' , {!!} , {!PE.cong (wkₜ ρ) A≡B!} , {!!} , {!!} ]
  wkEq ¹ ρ ⊢Δ (emb x) A≡B = wkEq ⁰ ρ ⊢Δ x A≡B

  wkTerm : ∀ {Γ Δ A t} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A]
         → Δ ⊩⟨ l ⟩ U.wkₜ ρ t ∷ U.wkₜ ρ A / wk l ρ ⊢Δ [A]
  wkTerm ⁰ ρ ⊢Δ (ℕ x) ℕ[ n , d , natN ] = ℕ[ wkₜ ρ n , T.wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN ]
  wkTerm ⁰ ρ ⊢Δ (ne x x₁) t₁ = T.wkTerm ρ ⊢Δ t₁
  wkTerm ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂) = (T.wkTerm ρ ⊢Δ proj₁) , (λ ρ₁ ⊢Δ₁ [a] a≡b → {!!})
  wkTerm ¹ ρ ⊢Δ U (proj₁ , proj₂) = (T.wkTerm ρ ⊢Δ proj₁) , (wk ⁰ ρ ⊢Δ proj₂)
  wkTerm ¹ ρ ⊢Δ ℕ ℕ[ n , d , natN ] = ℕ[ wkₜ ρ n , T.wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN ]
  wkTerm ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) t₁ = {!!}
  wkTerm ¹ ρ ⊢Δ (emb x) t₁ = wkTerm ⁰ ρ ⊢Δ x t₁

  wkEqTerm : ∀ {Γ Δ A t u} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
         → Δ ⊩⟨ l ⟩ U.wkₜ ρ t ≡ U.wkₜ ρ u ∷ U.wkₜ ρ A / wk l ρ ⊢Δ [A]
  wkEqTerm ⁰ ρ ⊢Δ (ℕ x) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] =
    ℕ≡[ wkₜ ρ k , wkₜ ρ k' , T.wkRed*Term ρ ⊢Δ d , T.wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] ]
  wkEqTerm ⁰ ρ ⊢Δ (ne x x₁) t≡u = T.wkEqTerm ρ ⊢Δ t≡u
  wkEqTerm ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) t≡u = {!!}
  wkEqTerm ¹ ρ ⊢Δ U U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = U[ T.wkTerm ρ ⊢Δ ⊢t , T.wkTerm ρ ⊢Δ ⊢u , T.wkEqTerm ρ ⊢Δ t≡u , wk ⁰ ρ ⊢Δ ⊩t , wk ⁰ ρ ⊢Δ ⊩u , wkEq ⁰ ρ ⊢Δ ⊩t [t≡u] ]
  wkEqTerm ¹ ρ ⊢Δ ℕ ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = ℕ≡[ wkₜ ρ k , wkₜ ρ k' , T.wkRed*Term ρ ⊢Δ d , T.wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] ]
  wkEqTerm ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) t≡u = {!!}
  wkEqTerm ¹ ρ ⊢Δ (emb x) t≡u = wkEqTerm ⁰ ρ ⊢Δ x t≡u
