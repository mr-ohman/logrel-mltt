module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.Reduction
open import Definition.Typed.EqualityRelation

open import Tools.Product


instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_≡_ _⊢_≡_∷_ _⊢_≡_∷_
                      refl app-cong natrec-cong sym
                      trans conv wkEqTerm (λ x → x)
                      (λ x → refl (U x)) (λ x → refl (ℕ x)) (λ x → refl (ℕ x))
                      (λ x → refl (zero x))
                      sym sym trans trans
                      reduction reductionₜ
                      wkEq wkEqTerm
                      (λ x → x) (λ x → x) conv univ
                      suc-cong Π-cong Π-cong
                      (λ x x₁ x₂ x₃ x₄ x₅ → fun-ext x x₁ x₂ x₅)
