{-# OPTIONS --without-K #-}

module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.Reduction
open import Definition.Typed.EqualityRelation

open import Tools.Product


-- Judgmental instance of the equality relation

instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_≡_ _⊢_≡_∷_ _⊢_≡_∷_
                      (λ x → x) (λ x → x) (λ x → x) univ
                      sym sym sym trans trans trans
                      conv conv wkEq wkEqTerm wkEqTerm
                      reduction reductionₜ
                      (λ x → refl (U x)) (λ x → refl (ℕ x)) (λ x → refl (ℕ x))
                      Π-cong Π-cong (λ x → refl (zero x)) suc-cong
                      (λ x x₁ x₂ x₃ x₄ x₅ → fun-ext x x₁ x₂ x₅)
                      refl app-cong natrec-cong
