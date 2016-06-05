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


open import Definition.LogicalRelation.Tactic
open import Relation.Nullary

mutual
  proof-irrelevanceEq : ∀ {Γ A B} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A ≡ B / q
  proof-irrelevanceEq l l' p q A≡B = proof-irrelevanceEqT (decRel l l' p q) A≡B

  proof-irrelevanceEq' : ∀ {Γ A A' B} l l' (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A' ≡ B / q
  proof-irrelevanceEq' l l' PE.refl p q A≡B = proof-irrelevanceEq l l' p q A≡B

  proof-irrelevanceEq'' : ∀ {Γ A A' B B'} l l' (eqA : A PE.≡ A') (eqB : B PE.≡ B') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                        → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A' ≡ B' / q
  proof-irrelevanceEq'' l l' PE.refl PE.refl p q A≡B = proof-irrelevanceEq l l' p q A≡B

  proof-irrelevanceEqT : ∀ {Γ A B} {l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                       → Dec (Tactic Γ A l l' p q)
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A ≡ B / q
  proof-irrelevanceEqT (yes (ℕ⁰⁰ D D₁)) B⇒*ℕ = B⇒*ℕ
  proof-irrelevanceEqT (yes (ℕ⁰¹ D ⊢Γ₁)) B⇒*ℕ = B⇒*ℕ
  proof-irrelevanceEqT (yes (ℕ¹⁰ ⊢Γ D₁)) B⇒*ℕ = B⇒*ℕ
  proof-irrelevanceEqT (yes (ℕ¹¹ ⊢Γ ⊢Γ₁)) B⇒*ℕ = B⇒*ℕ
  proof-irrelevanceEqT (yes (ne D neK D₁ neK₁)) ne[ M , D' , neM , K≡M ] = ne[ M , D' , neM , trans (sym (subset* (red D₁))) (trans (subset* (red D)) K≡M) ]
  proof-irrelevanceEqT (yes (Π⁰⁰ D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁))
                       Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
    in  Π⁰[ F' , G' , D' , A≡B
          , (λ ρ ⊢Δ → proof-irrelevanceEq' ⁰ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
          , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                           in  proof-irrelevanceEq' ⁰ ⁰ (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]
  proof-irrelevanceEqT (yes (Π⁰¹ D ⊢F ⊢G [F] [G] G-ext ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁))
                       Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
    in Π¹[ F' , G' , D' , A≡B
       , (λ ρ ⊢Δ → proof-irrelevanceEq' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
       , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                        in  proof-irrelevanceEq' ⁰ ¹ (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) (PE.sym G≡G₁)) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]
  proof-irrelevanceEqT (yes (Π¹⁰ ⊢F ⊢G ⊩F [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁))
                       Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D₁) Π)
    in Π⁰[ F' , G' , D' , A≡B
         , (λ ρ ⊢Δ → proof-irrelevanceEq' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
         , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                          in proof-irrelevanceEq' ¹ ⁰ (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]
  proof-irrelevanceEqT (yes (Π¹¹ ⊢F ⊢G ⊩F [F] [G] G-ext ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁))
                       Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    Π¹[ F' , G' , D' , A≡B
      , (λ ρ ⊢Δ → proof-irrelevanceEq ¹ ¹ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
      , (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm ¹ ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEq ¹ ¹ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]
  proof-irrelevanceEqT (yes U) B≡U = B≡U
  proof-irrelevanceEqT (yes (emb⁰¹ p₁)) A≡B = proof-irrelevanceEqT (yes p₁) A≡B
  proof-irrelevanceEqT (yes (emb¹⁰ p₁)) A≡B = proof-irrelevanceEqT (yes p₁) A≡B
  proof-irrelevanceEqT (no ¬p) A≡B = ⊥-elim (refuteRel _ _ _ _ ¬p)

--------------------------------------------------------------------------------

  proof-irrelevanceTerm : ∀ {Γ A t} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                        → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A / q
  proof-irrelevanceTerm l l' p q t = proof-irrelevanceTermT (decRel l l' p q) t

  proof-irrelevanceTerm' : ∀ {Γ A A' t} l l' (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A' / q
  proof-irrelevanceTerm' l l' PE.refl p q t = proof-irrelevanceTerm l l' p q t

  proof-irrelevanceTermT : ∀ {Γ A t} {l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                         → Dec (Tactic Γ A l l' p q)
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A / q
  proof-irrelevanceTermT (yes (ℕ⁰⁰ D D₁)) t = t
  proof-irrelevanceTermT (yes (ℕ⁰¹ D ⊢Γ₁)) t = t
  proof-irrelevanceTermT (yes (ℕ¹⁰ ⊢Γ D₁)) t = t
  proof-irrelevanceTermT (yes (ℕ¹¹ ⊢Γ ⊢Γ₁)) t = t
  proof-irrelevanceTermT (yes (ne D neK D₁ neK₁)) t = t
  proof-irrelevanceTermT (yes (Π⁰⁰ D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
                                   [a]         = proof-irrelevanceTerm' ⁰ ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b]       = proof-irrelevanceEqTerm' ⁰ ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm' ⁰ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))
  proof-irrelevanceTermT (yes (Π⁰¹ D ⊢F ⊢G [F] [G] G-ext ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁)) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
                                   [a]         = proof-irrelevanceTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b]       = proof-irrelevanceEqTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm' ⁰ ¹ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) (PE.sym G≡G₁)) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))
  proof-irrelevanceTermT (yes (Π¹⁰ ⊢F ⊢G ⊩F [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D₁) Π)
                                   [a]         = proof-irrelevanceTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b]       = proof-irrelevanceEqTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm' ¹ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))
  proof-irrelevanceTermT (yes (Π¹¹ ⊢F ⊢G ⊩F [F] [G] G-ext ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁)) (⊢t , [t]) =
    ⊢t , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let [a]   = proof-irrelevanceTerm ¹ ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                   [a≡b] = proof-irrelevanceEqTerm ¹ ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                               in  proof-irrelevanceEqTerm ¹ ¹ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [a≡b]))
  proof-irrelevanceTermT (yes U) t = t
  proof-irrelevanceTermT (yes (emb⁰¹ p₁)) t = proof-irrelevanceTermT (yes p₁) t
  proof-irrelevanceTermT (yes (emb¹⁰ p₁)) t = proof-irrelevanceTermT (yes p₁) t
  proof-irrelevanceTermT (no ¬p) t = ⊥-elim (refuteRel _ _ _ _ ¬p)

--------------------------------------------------------------------------------

  proof-irrelevanceEqTerm : ∀ {Γ A t u} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A / q
  proof-irrelevanceEqTerm l l' p q t≡u = proof-irrelevanceEqTermT (decRel l l' p q) t≡u

  proof-irrelevanceEqTerm' : ∀ {Γ A A' t u} l l' (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A' / q
  proof-irrelevanceEqTerm' l l' PE.refl p q t≡u = proof-irrelevanceEqTerm l l' p q t≡u

  proof-irrelevanceEqTerm'' : ∀ {Γ A A' t t' u u'} l l' (eqt : t PE.≡ t') (equ : u PE.≡ u') (eqA : A PE.≡ A')
                              (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t' ≡ u' ∷ A' / q
  proof-irrelevanceEqTerm'' l l' PE.refl PE.refl PE.refl p q t≡u = proof-irrelevanceEqTerm l l' p q t≡u

  proof-irrelevanceEqTermT : ∀ {Γ A t u} {l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                           → Dec (Tactic Γ A l l' p q)
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A / q
  proof-irrelevanceEqTermT (yes (ℕ⁰⁰ D D₁)) t≡u = t≡u
  proof-irrelevanceEqTermT (yes (ℕ⁰¹ D ⊢Γ₁)) t≡u = t≡u
  proof-irrelevanceEqTermT (yes (ℕ¹⁰ ⊢Γ D₁)) t≡u = t≡u
  proof-irrelevanceEqTermT (yes (ℕ¹¹ ⊢Γ ⊢Γ₁)) t≡u = t≡u
  proof-irrelevanceEqTermT (yes (ne D neK D₁ neK₁)) t≡u = t≡u
  proof-irrelevanceEqTermT (yes (Π⁰⁰ D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁))  (t≡u , ⊩t , ⊩u , [t≡u]) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
        [A]         = Π D ⊢F ⊢G [F] [G] G-ext
        [A]₁        = Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm ⁰ ⁰ [A] [A]₁ ⊩t , proof-irrelevanceTerm ⁰ ⁰ [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm' ⁰ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))
  proof-irrelevanceEqTermT (yes (Π⁰¹ D ⊢F ⊢G [F] [G] G-ext ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁)) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity ((whnfRed*' (red D) Π))
        [A]         = Π D ⊢F ⊢G [F] [G] G-ext
        [A]₁        = Π ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm ⁰ ¹ [A] [A]₁ ⊩t , proof-irrelevanceTerm ⁰ ¹ [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ¹ ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm' ⁰ ¹ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) (PE.sym G≡G₁)) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))
  proof-irrelevanceEqTermT (yes (Π¹⁰ ⊢F ⊢G ⊩F [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity ((whnfRed*' (red D₁) Π))
        [A]         = Π ⊢F ⊢G ⊩F [F] [G] G-ext
        [A]₁        = Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm ¹ ⁰ [A] [A]₁ ⊩t , proof-irrelevanceTerm ¹ ⁰ [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ ¹ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm' ¹ ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))
  proof-irrelevanceEqTermT (yes (Π¹¹ ⊢F ⊢G ⊩F [F] [G] G-ext ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁)) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let [A]  = Π ⊢F ⊢G ⊩F [F] [G] G-ext
        [A]₁ = Π ⊢F₁ ⊢G₁ ⊩F₁ [F]₁ [G]₁ G-ext₁
    in  t≡u , proof-irrelevanceTerm ¹ ¹ [A] [A]₁ ⊩t , proof-irrelevanceTerm ¹ ¹ [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm ¹ ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  proof-irrelevanceEqTerm ¹ ¹ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))
  proof-irrelevanceEqTermT (yes U) t≡u = t≡u
  proof-irrelevanceEqTermT (yes (emb⁰¹ p₁)) t≡u = proof-irrelevanceEqTermT (yes p₁) t≡u
  proof-irrelevanceEqTermT (yes (emb¹⁰ p₁)) t≡u = proof-irrelevanceEqTermT (yes p₁) t≡u
  proof-irrelevanceEqTermT (no ¬p) t≡u = ⊥-elim (refuteRel _ _ _ _ ¬p)
