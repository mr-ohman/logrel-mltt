module Definition.LogicalRelation.Properties.Conversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Soundness

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


mutual
  convTermT₁ : ∀ {l l' Γ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
             → Tactic Γ l l' A B [A] [B] → Γ ⊩⟨ l ⟩ A ≡ B / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊩⟨ l' ⟩ t ∷ B / [B]
  convTermT₁ (ℕ D D₁) A≡B ℕ[ n , d , natN , prop ] = ℕ[ n , d , natN , prop ]
  convTermT₁ {l} (ne D neK D₁ neK₁) A≡B t = conv t (soundnessEq {l} (ne D neK) A≡B)
  convTermT₁ (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] (⊢t , ⊩t) =
    conv ⊢t A≡B
    , (λ ρ ⊢Δ [a] [b] [a≡b] → let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
                                  [F≡F₁] = irrelevanceEq'' PE.refl (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F] ρ ⊢Δ) ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)
                                  [a]₁ = convTerm₂ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a]
                                  [b]₁ = convTerm₂ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [b]
                                  [a≡b]₁ = convEqTerm₂ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a≡b]
                                  [G≡G₁] = irrelevanceEq'' PE.refl (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) ([G] ρ ⊢Δ [a]₁) ([G] ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a]₁)
                              in  convEqTerm₁ ([G] ρ ⊢Δ [a]₁) ([G]₁ ρ ⊢Δ [a]) [G≡G₁] (⊩t ρ ⊢Δ [a]₁ [b]₁ [a≡b]₁))
  convTermT₁ (U ⊢Γ ⊢Γ₁) A≡B t = t
  convTermT₁ (emb⁰¹ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (emb¹⁰ x) A≡B t = convTermT₁ x A≡B t

  convTermT₂ : ∀ {l l' Γ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
           → Tactic Γ l l' A B [A] [B] → Γ ⊩⟨ l ⟩ A ≡ B / [A]
           → Γ ⊩⟨ l' ⟩ t ∷ B / [B] → Γ ⊩⟨ l ⟩ t ∷ A / [A]
  convTermT₂ (ℕ D D₁) A≡B ℕ[ n , d , natN , prop ] = ℕ[ n , d , natN , prop ]
  convTermT₂ {l} (ne D neK D₁ neK₁) A≡B t = conv t (sym (soundnessEq {l} (ne D neK) A≡B))
  convTermT₂ (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] (⊢t , ⊩t) =
    conv ⊢t (sym A≡B)
    , (λ ρ ⊢Δ [a] [b] [a≡b] → let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
                                  [F≡F₁] = irrelevanceEq'' PE.refl (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F] ρ ⊢Δ) ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)
                                  [a]₁ = convTerm₁ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a]
                                  [b]₁ = convTerm₁ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [b]
                                  [a≡b]₁ = convEqTerm₁ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a≡b]
                                  [G≡G₁] = irrelevanceEq'' PE.refl (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) ([G] ρ ⊢Δ [a]) ([G] ρ ⊢Δ [a]) ([G≡G'] ρ ⊢Δ [a])
                              in  convEqTerm₂ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) [G≡G₁] (⊩t ρ ⊢Δ [a]₁ [b]₁ [a≡b]₁))
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
                          [F≡F₁] = irrelevanceEq'' PE.refl (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F] ρ ⊢Δ) ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)
                          [a]₁ = convTerm₂ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a]
                          [G≡G₁] = irrelevanceEq'' PE.refl (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) ([G] ρ ⊢Δ [a]₁) ([G] ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a]₁)
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
                          [F≡F₁] = irrelevanceEq'' PE.refl (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F] ρ ⊢Δ) ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)
                          [a]₁ = convTerm₁ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [F≡F₁] [a]
                          [G≡G₁] = irrelevanceEq'' PE.refl (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) (PE.sym G₁≡G')) ([G] ρ ⊢Δ [a]) ([G] ρ ⊢Δ [a]) ([G≡G'] ρ ⊢Δ [a])
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
