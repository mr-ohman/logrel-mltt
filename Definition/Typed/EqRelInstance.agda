module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.EqualityRelation

reduction : ∀ {A A' B B' Γ}
          → Γ ⊢ A ⇒* A' → Γ ⊢ B ⇒* B' → Γ ⊢ A' ≡ B' → Γ ⊢ A ≡ B
reduction D D' A'≡B' = trans (subset* D) (trans A'≡B' (sym (subset* D')))

reductionₜ : ∀ {a a' b b' A B Γ}
           → Γ ⊢ A ⇒* B → Γ ⊢ a ⇒* a' ∷ B → Γ ⊢ b ⇒* b' ∷ B
           → Γ ⊢ a' ≡ b' ∷ B → Γ ⊢ a ≡ b ∷ A
reductionₜ D d d' a'≡b' =
  conv (trans (subset*Term d)
              (trans a'≡b' (sym (subset*Term d'))))
       (sym (subset* D))

eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_≡_ _⊢_≡_∷_
                      (λ x → refl (U x)) (λ x → refl (ℕ x))
                      sym sym trans trans
                      reduction reductionₜ wkEq wkEqTerm
                      (λ x → x) (λ x → x) conv
