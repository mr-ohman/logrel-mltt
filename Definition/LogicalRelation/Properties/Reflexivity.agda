module Definition.LogicalRelation.Properties.Reflexivity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE


reflEq : ∀ {l Γ A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq (U' l' l< ⊢Γ) = PE.refl
reflEq (ℕ D) = red D
reflEq (ne' K [ ⊢A , ⊢B , D ] neK) =
  ne₌ _ [ ⊢A , ⊢B , D ] neK (refl ⊢B)
reflEq (Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) =
  Π₌ _ _ D (refl ⊢A)
     (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
     (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq (emb 0<1 [A]) = reflEq [A]

reflNatural-prop : ∀ {Γ n} (natN : Natural n)
                 → natural-prop Γ n natN
                 → [Natural]-prop Γ n n
reflNatural-prop suc (ℕₜ n d natN prop) =
  suc (ℕₜ₌ n n d d (refl (_⊢_:⇒*:_∷_.⊢t d))
           (reflNatural-prop natN prop))
reflNatural-prop zero t = zero
reflNatural-prop (ne x) n = ne x x (refl n)

reflEqTerm : ∀ {l Γ A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm (U' ⁰ 0<1 ⊢Γ) (Uₜ ⊢t ⊩t) =
  Uₜ₌ ⊢t ⊢t (refl ⊢t) ⊩t ⊩t (reflEq ⊩t)
reflEqTerm (ℕ D) (ℕₜ n [ ⊢t , ⊢u , d ] natN prop) =
  ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] (refl ⊢t)
      (reflNatural-prop natN prop)
reflEqTerm (ne' K D neK) t = refl t
reflEqTerm (Π' F G D ⊢F ⊢G [F] [G] G-ext) (Πₜ ⊢t [t] [t]₁) =
  Πₜ₌ (refl ⊢t) (Πₜ ⊢t [t] [t]₁) (Πₜ ⊢t [t] [t]₁)
      (λ ρ ⊢Δ [a] → [t] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
