module Definition.LogicalRelation.Properties where

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Reflexivity
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Weakening

open import Tools.Context

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


open import Lemma.Soundness

mutual
  convTermT₁ : ∀ {l l' Γ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
             → Tactic Γ l l' A B [A] [B] → Γ ⊩⟨ l ⟩ A ≡ B / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊩⟨ l' ⟩ t ∷ B / [B]
  convTermT₁ (ℕ D D₁) A≡B ℕ[ n , d , natN ] = ℕ[ n , d , natN ]
  convTermT₁ {l} (ne D neK D₁ neK₁) A≡B t = conv t (soundnessEq {l} (ne D neK) A≡B)
  convTermT₁ (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] (⊢t , ⊩t) =
    conv ⊢t A≡B
    , (λ ρ ⊢Δ [a] [a≡b] → let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
                              [F≡F₁] = proof-irrelevanceEq'' PE.refl (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F] ρ ⊢Δ) ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)
                              [a]₁ = convTerm₂ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a]
                              [a≡b]₁ = convEqTerm₂ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a≡b]
                              [G≡G₁] = proof-irrelevanceEq'' PE.refl (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) ([G] ρ ⊢Δ [a]₁) ([G] ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a]₁)
                          in  convEqTerm₁ ([G] ρ ⊢Δ [a]₁) ([G]₁ ρ ⊢Δ [a]) [G≡G₁] (⊩t ρ ⊢Δ [a]₁ [a≡b]₁))
  convTermT₁ (U ⊢Γ ⊢Γ₁) A≡B t = t
  convTermT₁ (emb⁰¹ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (emb¹⁰ x) A≡B t = convTermT₁ x A≡B t

  convTermT₂ : ∀ {l l' Γ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
           → Tactic Γ l l' A B [A] [B] → Γ ⊩⟨ l ⟩ A ≡ B / [A]
           → Γ ⊩⟨ l' ⟩ t ∷ B / [B] → Γ ⊩⟨ l ⟩ t ∷ A / [A]
  convTermT₂ (ℕ D D₁) A≡B ℕ[ n , d , natN ] = ℕ[ n , d , natN ]
  convTermT₂ {l} (ne D neK D₁ neK₁) A≡B t = conv t (sym (soundnessEq {l} (ne D neK) A≡B))
  convTermT₂ (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] (⊢t , ⊩t) =
    conv ⊢t (sym A≡B)
    , (λ ρ ⊢Δ [a] [a≡b] → let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
                              [F≡F₁] = proof-irrelevanceEq'' PE.refl (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F] ρ ⊢Δ) ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)
                              [a]₁ = convTerm₁ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a]
                              [a≡b]₁ = convEqTerm₁ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a≡b]
                              [G≡G₁] = proof-irrelevanceEq'' PE.refl (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) ([G] ρ ⊢Δ [a]) ([G] ρ ⊢Δ [a]) ([G≡G'] ρ ⊢Δ [a])
                          in  convEqTerm₂ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) [G≡G₁] (⊩t ρ ⊢Δ [a]₁ [a≡b]₁))
  convTermT₂ (U ⊢Γ ⊢Γ₁) A≡B t = t
  convTermT₂ (emb⁰¹ x) A≡B t = convTermT₂ x A≡B t
  convTermT₂ (emb¹⁰ x) A≡B t = convTermT₂ x A≡B t

  convTerm₁ : ∀ {Γ A B t l l'} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊩⟨ l' ⟩ t ∷ B / [B]
  convTerm₁ [A] [B] A≡B t = convTermT₁ (goodCases [A] [B] A≡B) A≡B t

  convTerm₂ : ∀ {Γ A B t l l'} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A]
          → Γ ⊩⟨ l' ⟩ t ∷ B / [B] → Γ ⊩⟨ l ⟩ t ∷ A / [A]
  convTerm₂ [A] [B] A≡B t = convTermT₂ (goodCases [A] [B] A≡B) A≡B t

  convEqTermT₁ : ∀ {l l' Γ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
               → Tactic Γ l l' A B [A] [B] → Γ ⊩⟨ l ⟩ A ≡ B / [A]
               → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊩⟨ l' ⟩ t ≡ u ∷ B / [B]
  convEqTermT₁ (ℕ D D₁) A≡B ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ]
  convEqTermT₁ {l} (ne D neK D₁ neK₁) A≡B t≡u = conv t≡u (soundnessEq {l} (ne D neK) A≡B)
  convEqTermT₁ (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] (t≡u , ⊩t , ⊩u , [t≡u]) =
    let [A] = Π D ⊢F ⊢G [F] [G] G-ext
        [B] = Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ]
    in  conv t≡u A≡B , convTerm₁ [A] [B] [A≡B] ⊩t , convTerm₁ [A] [B] [A≡B] ⊩u
     ,  (λ ρ ⊢Δ [a] → let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
                          [F≡F₁] = proof-irrelevanceEq'' PE.refl (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F] ρ ⊢Δ) ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)
                          [a]₁ = convTerm₂ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a]
                          [G≡G₁] = proof-irrelevanceEq'' PE.refl (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) ([G] ρ ⊢Δ [a]₁) ([G] ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a]₁)
                      in  convEqTerm₁ ([G] ρ ⊢Δ [a]₁) ([G]₁ ρ ⊢Δ [a]) [G≡G₁] ([t≡u] ρ ⊢Δ [a]₁))
  convEqTermT₁ (U ⊢Γ ⊢Γ₁) A≡B t≡u = t≡u
  convEqTermT₁ (emb⁰¹ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  convEqTermT₁ (emb¹⁰ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u

  convEqTermT₂ : ∀ {l l' Γ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
             → Tactic Γ l l' A B [A] [B] → Γ ⊩⟨ l ⟩ A ≡ B / [A]
             → Γ ⊩⟨ l' ⟩ t ≡ u ∷ B / [B] → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
  convEqTermT₂ (ℕ D D₁) A≡B ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ]
  convEqTermT₂ {l} (ne D neK D₁ neK₁) A≡B t≡u = conv t≡u (sym (soundnessEq {l} (ne D neK) A≡B))
  convEqTermT₂ (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] (t≡u , ⊩t , ⊩u , [t≡u]) =
    let [A] = Π D ⊢F ⊢G [F] [G] G-ext
        [B] = Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ]
    in  conv t≡u (sym A≡B) , convTerm₂ [A] [B] [A≡B] ⊩t , convTerm₂ [A] [B] [A≡B] ⊩u
     ,  (λ ρ ⊢Δ [a] → let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
                          [F≡F₁] = proof-irrelevanceEq'' PE.refl (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F] ρ ⊢Δ) ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)
                          [a]₁ = convTerm₁ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a]
                          [G≡G₁] = proof-irrelevanceEq'' PE.refl (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) ([G] ρ ⊢Δ [a]) ([G] ρ ⊢Δ [a]) ([G≡G'] ρ ⊢Δ [a])
                      in  convEqTerm₂ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) [G≡G₁] ([t≡u] ρ ⊢Δ [a]₁))
  convEqTermT₂ (U ⊢Γ ⊢Γ₁) A≡B t≡u = t≡u
  convEqTermT₂ (emb⁰¹ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  convEqTermT₂ (emb¹⁰ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u

  convEqTerm₁ : ∀ {l l' Γ A B t u} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
              → Γ ⊩⟨ l ⟩ A ≡ B / [A]
              → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊩⟨ l' ⟩ t ≡ u ∷ B / [B]
  convEqTerm₁ [A] [B] A≡B t≡u = convEqTermT₁ (goodCases [A] [B] A≡B) A≡B t≡u

  convEqTerm₂ : ∀ {l l' Γ A B t u} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊩⟨ l' ⟩ t ≡ u ∷ B / [B] → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
  convEqTerm₂ [A] [B] A≡B t≡u = convEqTermT₂ (goodCases [A] [B] A≡B) A≡B t≡u

mutual
  symEqT : ∀ {Γ A B l l'} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B} → Tactic Γ l l' A B [A] [B] → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symEqT (ℕ D D₁) A≡B = red D
  symEqT (ne D neK D₁ neK₁) ne[ M , D' , neM , K≡M ] = ne[ _ , D , neK , trans (sym (subset* (red D₁))) (trans (subset* (red D')) (sym K≡M)) ]
  symEqT (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
    in  Π¹[ _ , _ , red D , sym A≡B
          , (λ ρ ⊢Δ → proof-irrelevanceEq' (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)) ([F]₁ ρ ⊢Δ) (symEq ([F] ρ ⊢Δ) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)) ([F≡F'] ρ ⊢Δ)))
          , (λ ρ ⊢Δ [a] → let [a]₁ = convTerm₁ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) (proof-irrelevanceEq' (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)) ([F]₁ ρ ⊢Δ) (symEq ([F] ρ ⊢Δ) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)) ([F≡F'] ρ ⊢Δ))) [a]
                          in  proof-irrelevanceEq' (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkLiftₜ ρ x [ _ ]) G₁≡G' ([G]₁ ρ ⊢Δ [a])) ([G]₁ ρ ⊢Δ [a]) (symEq ([G] ρ ⊢Δ [a]₁) (PE.subst (λ x → _ ⊩⟨ _ ⟩ wkLiftₜ ρ x [ _ ]) G₁≡G' ([G]₁ ρ ⊢Δ [a])) ([G≡G'] ρ ⊢Δ [a]₁))) ]
  symEqT (U ⊢Γ ⊢Γ₁) A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  symEq : ∀ {Γ A B l l'} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

reflNatural : ∀ {Γ n} → Natural n → Γ ⊢ n ≡ n ∷ ℕ → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) n n
reflNatural (suc natN) eq = suc (reflNatural natN {!!})
reflNatural zero eq = zero
reflNatural (ne x) eq = ne x x eq

symNatural : ∀ {Γ m n} → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) m n → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) n m
symNatural (suc n₁) = suc (symNatural n₁)
symNatural zero = zero
symNatural (ne x x₁ x₂) = ne x₁ x (sym x₂)

reflEqTerm : ∀ {l Γ A t} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm {⁰} (U {l< = ()} ⊢Γ) (⊢t , ⊩t)
reflEqTerm {¹} (U {l< = 0<1} ⊢Γ) (⊢t , ⊩t) = U[ ⊢t , ⊢t , refl ⊢t , ⊩t , ⊩t , reflEq ⊩t ]
reflEqTerm (ℕ D) ℕ[ n , [ ⊢t , ⊢u , d ] , natN ] = ℕ≡[ n , n , d , d , refl ⊢t , reflNatural natN (refl ⊢u) ]
reflEqTerm (ne D neK) t = refl t
reflEqTerm (Π D ⊢F ⊢G [F] [G] G-ext) (⊢t , [t]) = refl ⊢t , (⊢t , [t]) , (⊢t , [t]) , (λ ρ ⊢Δ [a] → reflEqTerm ([G] ρ ⊢Δ [a]) {!!})
reflEqTerm {⁰} (emb {l< = ()} x) t
reflEqTerm {¹} (emb {l< = 0<1} x) t = reflEqTerm x t

symEqTerm : ∀ {l Γ A t u} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊩⟨ l ⟩ u ≡ t ∷ A / [A]
symEqTerm (U ⊢Γ) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = U[ ⊢u , ⊢t , sym t≡u , ⊩u , ⊩t , {!!} ]
symEqTerm (ℕ D) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = ℕ≡[ k' , k , d' , d , sym t≡u , symNatural [k≡k'] ]
symEqTerm (ne D neK) t≡u = sym t≡u
symEqTerm (Π D ⊢F ⊢G [F] [G] G-ext) t≡u = {!!}
symEqTerm {⁰} (emb {l< = ()} x) t≡u
symEqTerm {¹} (emb {l< = 0<1} x) t≡u = symEqTerm x t≡u

-- reflEq : ∀ {Γ A} l ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
-- reflEq ⁰ (ℕ [ ⊢A , ⊢B , D ]) = D
-- reflEq ⁰ (ne [ ⊢A , ⊢B , D ] neK) = ne[ _ , [ ⊢A , ⊢B , D ] , neK , (refl ⊢B) ]
-- reflEq ⁰ (Π {F} {G} [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) =
--   Π⁰[ F , G , D , refl ⊢A , (λ ρ ⊢Δ → reflEq ⁰ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ⁰ ([G] ρ ⊢Δ [a])) ]
-- reflEq ¹ U = PE.refl
-- reflEq ¹ (ℕ ⊢Γ) = id (ℕ ⊢Γ)
-- reflEq ¹ (Π ⊢F ⊢G ⊩F [F] [G] G-ext) = Π¹[ _ , _ , id (Π ⊢F ▹ ⊢G) , refl (Π ⊢F ▹ ⊢G) , (λ ρ ⊢Δ → reflEq ¹ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ¹ ([G] ρ ⊢Δ [a])) ]
-- reflEq ¹ (emb x) = reflEq ⁰ x
