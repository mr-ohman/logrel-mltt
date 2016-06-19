module Definition.LogicalRelation.PropertiesWIP where

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties

open import Tools.Context

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


substEq : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l ⟩ B
substEq (U {l< = l<} ⊢Γ) PE.refl = U {l< = l<} ⊢Γ
substEq (ℕ D) A≡B = ℕ {!D!}
substEq (ne D neK) ne[ M , D' , neM , K≡M ] = ne D' neM
substEq (Π {F} {G} D ⊢F ⊢G [F] [G] G-ext) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  Π {F = F'} {G = G'} {!D'!} {!!} {!!}
    (λ ρ ⊢Δ → substEq ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
    (λ ρ ⊢Δ [a] → let [a]₁ = convTerm₂ ([F] ρ ⊢Δ) (substEq ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)) ([F≡F'] ρ ⊢Δ) [a]
                  in  substEq ([G] ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a]₁))
    (λ ρ ⊢Δ [a] [a≡b] → {!!})
substEq {⁰} (emb {l< = ()} x) A≡B
substEq {¹} (emb {l< = 0<1} x) A≡B = emb {l< = 0<1} (substEq x A≡B)


-- reflEq : ∀ {Γ A} l ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
-- reflEq ⁰ (ℕ [ ⊢A , ⊢B , D ]) = D
-- reflEq ⁰ (ne [ ⊢A , ⊢B , D ] neK) = ne[ _ , [ ⊢A , ⊢B , D ] , neK , (refl ⊢B) ]
-- reflEq ⁰ (Π {F} {G} [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) =
--   Π⁰[ F , G , D , refl ⊢A , (λ ρ ⊢Δ → reflEq ⁰ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ⁰ ([G] ρ ⊢Δ [a])) ]
-- reflEq ¹ U = PE.refl
-- reflEq ¹ (ℕ ⊢Γ) = id (ℕ ⊢Γ)
-- reflEq ¹ (Π ⊢F ⊢G ⊩F [F] [G] G-ext) = Π¹[ _ , _ , id (Π ⊢F ▹ ⊢G) , refl (Π ⊢F ▹ ⊢G) , (λ ρ ⊢Δ → reflEq ¹ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ¹ ([G] ρ ⊢Δ [a])) ]
-- reflEq ¹ (emb x) = reflEq ⁰ x
