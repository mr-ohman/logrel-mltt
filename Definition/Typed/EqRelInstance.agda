{-# OPTIONS --without-K #-}

module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.Reduction
open import Definition.Typed.EqualityRelation

open import Tools.Function


-- Judgmental instance of the equality relation

instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_≡_ _⊢_≡_∷_ _⊢_≡_∷_
                      idᶠ idᶠ idᶠ univ
                      sym sym sym trans trans trans
                      conv conv wkEq wkEqTerm wkEqTerm
                      reduction reductionₜ
                      (refl ∘ᶠ U) (refl ∘ᶠ ℕ) (refl ∘ᶠ ℕ)
                      Π-cong Π-cong (refl ∘ᶠ zero) suc-cong
                      (λ x x₁ x₂ x₃ x₄ x₅ → η-eq x x₁ x₂ x₅)
                      refl app-cong natrec-cong
