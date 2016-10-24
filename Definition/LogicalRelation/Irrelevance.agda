module Definition.LogicalRelation.Irrelevance where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


irrelevanceNatural-prop : ∀ {Γ n n' m m'}
                        → n PE.≡ n' → m PE.≡ m'
                        → ([n≡m] : [Natural] n m) ([n'≡m'] : [Natural] n' m')
                        → [Natural]-prop Γ n m [n≡m]
                        → [Natural]-prop Γ n' m' [n'≡m']
irrelevanceNatural-prop PE.refl PE.refl suc suc prop = prop
irrelevanceNatural-prop PE.refl PE.refl suc (ne () x₁) prop
irrelevanceNatural-prop PE.refl PE.refl zero zero t = t
irrelevanceNatural-prop PE.refl PE.refl zero (ne () x₁) prop
irrelevanceNatural-prop PE.refl PE.refl (ne () x₁) suc prop
irrelevanceNatural-prop PE.refl PE.refl (ne () x₁) zero prop
irrelevanceNatural-prop PE.refl PE.refl (ne x x₁) (ne x₂ x₃) prop = prop

irrelevance' : ∀ {A A' Γ l}
             → A PE.≡ A'
             → Γ ⊩⟨ l ⟩ A
             → Γ ⊩⟨ l ⟩ A'
irrelevance' PE.refl [A] = [A]

irrelevanceΓ' : ∀ {l A A' Γ Γ'}
              → Γ PE.≡ Γ'
              → A PE.≡ A'
              → Γ  ⊩⟨ l ⟩ A
              → Γ' ⊩⟨ l ⟩ A'
irrelevanceΓ' PE.refl PE.refl [A] = [A]

mutual
  irrelevanceEq : ∀ {Γ A B l l'} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A ≡ B / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  irrelevanceEq' : ∀ {Γ A A' B l l'} (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A' ≡ B / q
  irrelevanceEq' PE.refl p q A≡B = irrelevanceEq p q A≡B

  irrelevanceEq'' : ∀ {Γ A A' B B' l l'} (eqA : A PE.≡ A') (eqB : B PE.≡ B') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                        → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A' ≡ B' / q
  irrelevanceEq'' PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  irrelevanceEqR' : ∀ {Γ A B B' l} (eqB : B PE.≡ B') (p : Γ ⊩⟨ l ⟩ A)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l ⟩ A ≡ B' / p
  irrelevanceEqR' PE.refl p A≡B = A≡B

  irrelevanceEqLift'' : ∀ {Γ A A' B B' C C' l l'} (eqA : A PE.≡ A') (eqB : B PE.≡ B') (eqC : C PE.≡ C') (p : Γ ∙ C ⊩⟨ l ⟩ A) (q : Γ ∙ C' ⊩⟨ l' ⟩ A')
                        → Γ ∙ C ⊩⟨ l ⟩ A ≡ B / p → Γ ∙ C' ⊩⟨ l' ⟩ A' ≡ B' / q
  irrelevanceEqLift'' PE.refl PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  irrelevanceEqT : ∀ {Γ A B l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                       → Tactic Γ l l' A A p q
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A ≡ B / q
  irrelevanceEqT (ℕ ℕA ℕB) A≡B = A≡B
  irrelevanceEqT (ne (ne K D neK) (ne K₁ D₁ neK₁)) ne[ M , D' , neM , K≡M ] = ne[ M , D' , neM , (trans (sym (subset* (red D₁))) (trans (subset* (red D)) K≡M)) ]
  irrelevanceEqT (Π (Π F G D ⊢F ⊢G [F] [G] G-ext) (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
    in  Π¹[ F' , G' , D' , A≡B
          , (λ ρ ⊢Δ → irrelevanceEq' (PE.cong (wkₜ ρ) F≡F₁) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
          , (λ ρ ⊢Δ [a]₁ → let [a] = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                           in  irrelevanceEq' (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a])) ]
  irrelevanceEqT (U UA UB) A≡B = A≡B
  irrelevanceEqT (emb⁰¹ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb¹⁰ x) A≡B = irrelevanceEqT x A≡B

--------------------------------------------------------------------------------

  irrelevanceTerm : ∀ {Γ A t l l'} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                        → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A / q
  irrelevanceTerm p q t = irrelevanceTermT (goodCasesRefl p q) t

  irrelevanceTerm' : ∀ {Γ A A' t l l'} (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A' / q
  irrelevanceTerm' PE.refl p q t = irrelevanceTerm p q t

  irrelevanceTerm'' : ∀ {Γ A A' t t' l l'}
                            (eqA : A PE.≡ A') (eqt : t PE.≡ t')
                            (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                          → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t' ∷ A' / q
  irrelevanceTerm'' PE.refl PE.refl p q t = irrelevanceTerm p q t

  irrelevanceTermΓ'' : ∀ {l l' A A' t t' Γ Γ'}
                     → Γ PE.≡ Γ'
                     → A PE.≡ A'
                     → t PE.≡ t'
                     → ([A]  : Γ  ⊩⟨ l  ⟩ A)
                       ([A'] : Γ' ⊩⟨ l' ⟩ A')
                     → Γ  ⊩⟨ l  ⟩ t ∷ A  / [A]
                     → Γ' ⊩⟨ l' ⟩ t' ∷ A' / [A']
  irrelevanceTermΓ'' PE.refl PE.refl PE.refl [A] [A'] [t] = irrelevanceTerm [A] [A'] [t]

  irrelevanceTermT : ∀ {Γ A t l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                         → Tactic Γ l l' A A p q
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A / q
  irrelevanceTermT (ℕ ℕA ℕB) t = t
  irrelevanceTermT (ne neA neB) t = t
  irrelevanceTermT (Π (Π F G D ⊢F ⊢G [F] [G] G-ext) (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)) (⊢t , [t] , [t]₁) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
    in  ⊢t , (λ ρ ⊢Δ [a]₁ [b]₁ [a≡b]₁ → let [a]   = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                                            [b]   = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [b]₁
                                            [a≡b] = irrelevanceEqTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
                                        in  irrelevanceEqTerm' (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t] ρ ⊢Δ [a] [b] [a≡b]))
       , (λ ρ ⊢Δ [a]₁ → let [a] = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  irrelevanceTerm' (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t]₁ ρ ⊢Δ [a]))
  irrelevanceTermT (U (U .⁰ 0<1 ⊢Γ) (U .⁰ 0<1 ⊢Γ₁)) t = t
  irrelevanceTermT (emb⁰¹ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb¹⁰ x) t = irrelevanceTermT x t

--------------------------------------------------------------------------------

  irrelevanceEqTerm : ∀ {Γ A t u l l'} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  irrelevanceEqTerm' : ∀ {Γ A A' t u l l'} (eq : A PE.≡ A') (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A' / q
  irrelevanceEqTerm' PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  irrelevanceEqTerm'' : ∀ {Γ A A' t t' u u' l l'} (eqt : t PE.≡ t') (equ : u PE.≡ u') (eqA : A PE.≡ A')
                              (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A')
                            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t' ≡ u' ∷ A' / q
  irrelevanceEqTerm'' PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  irrelevanceEqTermT : ∀ {Γ A t u} {l l'} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l' ⟩ A}
                           → Tactic Γ l l' A A p q
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A / q
  irrelevanceEqTermT (ℕ ℕA ℕB) t≡u = t≡u
  irrelevanceEqTermT (ne neA neB) t≡u = t≡u
  irrelevanceEqTermT (Π (Π F G D ⊢F ⊢G [F] [G] G-ext) (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red D , Π) (red D₁ , Π))
        [A]         = Π (Π F G D ⊢F ⊢G [F] [G] G-ext)
        [A]₁        = Π (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
    in  t≡u , irrelevanceTerm [A] [A]₁ ⊩t , irrelevanceTerm [A] [A]₁ ⊩u
     ,  (λ ρ ⊢Δ [a]₁ → let [a] = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
                       in  irrelevanceEqTerm' (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([t≡u] ρ ⊢Δ [a]))
  irrelevanceEqTermT (U (U .⁰ 0<1 ⊢Γ) (U .⁰ 0<1 ⊢Γ₁)) t≡u = t≡u
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
