module Definition.Conversion.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion
open import Definition.Conversion.Reduction
open import Definition.Conversion.Universe
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Lift
open import Definition.Conversion.Transitivity
open import Definition.Conversion.Weakening
open import Definition.EqualityRelation
open import Definition.LogicalRelation.Consequences.Syntactic

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_[conv↑]_ _⊢_[conv↑]_∷_
                      (λ x → liftConv (U-refl x))
                      (λ x → liftConv (ℕ-refl x))
                      (λ x → liftConvTerm (univ (ℕ x) (ℕ x) (ℕ-refl x)))
                      {!!} {!!}
                      {!!} {!!}
                      (λ x → liftConvTerm (zero-refl x))
                      {!!}
                      {!!} {!!}
                      transConv transConvTerm
                      (λ x x₁ x₂ → reductionConv↑ x x₁ {!!} {!!} x₂)
                      (λ x x₁ x₂ x₃ → reductionConv↑Term x x₁ x₂ {!!} {!!} {!!} x₃)
                      wkConv↑ wkConv↑Term
                      soundnessConv↑ soundnessConv↑Term
                      {!!} univConv↑
                      {!!} {!!}
                      (λ x → liftConvTerm (suc-cong x))
                      (λ x x₁ x₂ → liftConv (Π-cong x x₁ x₂))
                      (λ x x₁ x₂ →
                         let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
                             _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
                             ⊢Γ = wfTerm F∷U
                             F<>H = univConv↑ x₁
                             G<>E = univConv↑ x₂
                             F≡H = soundnessConv↑ F<>H
                             E∷U' = stabilityTerm (reflConEq ⊢Γ ∙ F≡H) E∷U
                         in  liftConvTerm (univ (Π F∷U ▹ G∷U) (Π H∷U ▹ E∷U')
                                                (Π-cong x F<>H G<>E)))
                      {!!}
                      (λ x x₁ x₂ x₃ → liftConvTerm (fun-ext x x₁ x₂ {!!} {!!} x₃))
