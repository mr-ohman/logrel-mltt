{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reflexivity {{eqrel : EqRelSet}} where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Tools.Nat
open import Tools.Product
open import Tools.Sum
  using (_⊎_ ; inj₁ ; inj₂)
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Reflexivity of reducible types.
reflEq : ∀ {l A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq (Uᵣ′ l′ l< ⊢Γ) = PE.refl
reflEq (ℕᵣ D) = red D
reflEq (Emptyᵣ D) = red D
reflEq (Unitᵣ D) = red D
reflEq (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) =
  ne₌ _ [ ⊢A , ⊢B , D ] neK K≡K
reflEq (Bᵣ′ W F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) =
   B₌ _ _ D A≡A
      (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
      (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) =
  ∪₌ _ _ (red D) A≡A
     (λ p ⊢Δ → reflEq ([S] p ⊢Δ))
     (λ [ρ] ⊢Δ → reflEq ([T] [ρ] ⊢Δ))
reflEq (∥ᵣ′ S D ⊢S A≡A [S]) =
  ∥₌ _ (red D) A≡A
     (λ p ⊢Δ → reflEq ([S] p ⊢Δ))
reflEq (emb 0<1 [A]) = reflEq [A]

reflNatural-prop : ∀ {n}
                 → Natural-prop Γ n
                 → [Natural]-prop Γ n n
reflNatural-prop (sucᵣ (ℕₜ n d t≡t prop)) =
  sucᵣ (ℕₜ₌ n n d d t≡t
            (reflNatural-prop prop))
reflNatural-prop zeroᵣ = zeroᵣ
reflNatural-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

reflEmpty-prop : ∀ {n}
                 → Empty-prop Γ n
                 → [Empty]-prop Γ n n
reflEmpty-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

reflUnit-prop : ∀ {n}
              → Unit-prop Γ n
              → [Unit]-prop Γ n n
reflUnit-prop h = h , h
{--
reflUnit-prop starᵣ = starᵣ
reflUnit-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)
--}

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {l A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [A]) =
  Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A])
reflEqTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflNatural-prop prop)
reflEqTerm (Emptyᵣ D) (Emptyₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  Emptyₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
    (reflEmpty-prop prop)
reflEqTerm (Unitᵣ D) (Unitₜ n [ ⊢t , ⊢u , d ] k≡k prop) =
  Unitₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] k≡k (reflUnit-prop prop) -- ⊢t ⊢t
reflEqTerm (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f [t] [t]
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Σₜ p d pProd p≅p [fst] [snd]) =
  Σₜ₌ p p d d pProd pProd p≅p [t] [t] [fst] [fst]
    (reflEqTerm ([F] id (wf ⊢F)) [fst])
    (reflEqTerm ([G] id (wf ⊢F) [fst]) [snd])
reflEqTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) [t]@(∪₁ₜ p b c pa i x) =
  ∪₁ₜ₌ p p b b c [t] [t] pa pa i i (reflEqTerm ([S] id (wf ⊢S)) x)
reflEqTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) [t]@(∪₂ₜ p b c pa i x) =
  ∪₂ₜ₌ p p b b c [t] [t] pa pa i i (reflEqTerm ([T] id (wf ⊢T)) x)
reflEqTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) [t]@(∪₃ₜ p b c (neNfₜ neK ⊢k k≡k)) =
  ∪₃ₜ₌ p p b b c [t] [t] (neNfₜ₌ neK neK k≡k)
reflEqTerm (∥ᵣ′ S D ⊢S A≡A [S]) [t]@(∥₁ₜ p b c pa i x) =
  ∥₁ₜ₌ p p b b c [t] [t] pa pa i i (reflEqTerm ([S] id (wf ⊢S)) x)
reflEqTerm (∥ᵣ′ S D ⊢S A≡A [S]) [t]@(∥₂ₜ p b c (neNfₜ neK ⊢k k≡k)) =
  ∥₂ₜ₌ p p b b c [t] [t] (neNfₜ₌ neK neK k≡k)
reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
