{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties as T
open import Definition.LogicalRelation
open import Definition.LogicalRelation.EqView
open import Definition.LogicalRelation.Irrelevance

open import Tools.Product
open import Tools.Empty


-- Helper function for sound terms of type U for specific type derivations.
univEq′ : ∀ {l Γ A} ([U] : Γ ⊩⟨ l ⟩U) → Γ ⊩⟨ l ⟩ A ∷ U / U-intr [U] → Γ ⊩⟨ ⁰ ⟩ A
univEq′ (noemb (U .⁰ 0<1 ⊢Γ)) (Uₜ A₁ d typeA A≡A [A]) = [A]
univEq′ (emb 0<1 x) [A] = univEq′ x [A]

-- Sound terms of type U are sound types.
univEq : ∀ {l Γ A} ([U] : Γ ⊩⟨ l ⟩ U) → Γ ⊩⟨ l ⟩ A ∷ U / [U] → Γ ⊩⟨ ⁰ ⟩ A
univEq [U] [A] = univEq′ (U-elim [U])
                         (irrelevanceTerm [U] (U-intr (U-elim [U])) [A])

-- Helper function for sound term equality of type U for specific type derivations.
univEqEq′ : ∀ {l l′ Γ A B} ([U] : Γ ⊩⟨ l ⟩U) ([A] : Γ ⊩⟨ l′ ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B ∷ U / U-intr [U]
         → Γ ⊩⟨ l′ ⟩ A ≡ B / [A]
univEqEq′ (noemb (U .⁰ 0<1 ⊢Γ)) [A]
          (Uₜ₌ A₁ B₁ d d′ typeA typeB A≡B [t] [u] [t≡u]) =
  irrelevanceEq [t] [A] [t≡u]
univEqEq′ (emb 0<1 x) [A] [A≡B] = univEqEq′ x [A] [A≡B]

-- Sound term equality of type U is sound type equality.
univEqEq : ∀ {l l′ Γ A B} ([U] : Γ ⊩⟨ l ⟩ U) ([A] : Γ ⊩⟨ l′ ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B ∷ U / [U]
         → Γ ⊩⟨ l′ ⟩ A ≡ B / [A]
univEqEq [U] [A] [A≡B] =
  let [A≡B]′ = irrelevanceEqTerm [U] (U-intr (U-elim [U])) [A≡B]
  in  univEqEq′ (U-elim [U]) [A] [A≡B]′
