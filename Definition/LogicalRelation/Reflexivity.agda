module Definition.LogicalRelation.Reflexivity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Context

import Relation.Binary.PropositionalEquality as PE


reflEq : ∀ {l Γ A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq (U ⊢Γ) = PE.refl
reflEq (ℕ D) = red D
reflEq (ne [ ⊢A , ⊢B , D ] neK) = ne[ _ , [ ⊢A , ⊢B , D ] , neK , refl ⊢B ]
reflEq (Π [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) = Π¹[ _ , _ , D , refl ⊢A , (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])) ]
reflEq {⁰} (emb {l< = ()} x)
reflEq {¹} (emb {l< = 0<1} x) = reflEq x
