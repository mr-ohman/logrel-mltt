{-# OPTIONS --without-K #-}

open import Definition.EqualityRelation

module Definition.LogicalRelation.Properties.Reflexivity {{eqrel : EqRelSet}} where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE


reflEq : ∀ {l Γ A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq (U' l' l< ⊢Γ) = PE.refl
reflEq (ℕ D) = red D
reflEq (ne' K [ ⊢A , ⊢B , D ] neK K≡K) =
  ne₌ _ [ ⊢A , ⊢B , D ] neK K≡K
reflEq (Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) =
  Π₌ _ _ D A≡A
     (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
     (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq (emb 0<1 [A]) = reflEq [A]

reflNatural-prop : ∀ {Γ n} (natN : Natural n)
                 → natural-prop Γ n natN
                 → [Natural]-prop Γ n n
reflNatural-prop suc (ℕₜ n d t≡t natN prop) =
  suc (ℕₜ₌ n n d d t≡t
           (reflNatural-prop natN prop))
reflNatural-prop zero t = zero
reflNatural-prop (ne x) (neNfₜ neK ⊢k k≡k) = ne (neNfₜ₌ neK neK k≡k)

reflEqTerm : ∀ {l Γ A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm (U' ⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [A]) =
  Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A])
reflEqTerm (ℕ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t natN prop) =
  ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflNatural-prop natN prop)
reflEqTerm (ne' K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f
      (Πₜ f d funcF f≡f [f] [f]₁)
      (Πₜ f d funcF f≡f [f] [f]₁)
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
