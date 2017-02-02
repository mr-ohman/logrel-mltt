module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.EqualityRelation

open import Tools.Product

reduction : ∀ {A A' B B' Γ}
          → Γ ⊢ A ⇒* A'
          → Γ ⊢ B ⇒* B'
          → Whnf A'
          → Whnf B'
          → Γ ⊢ A' ≡ B'
          → Γ ⊢ A ≡ B
reduction D D' whnfA' whnfB' A'≡B' =
  trans (subset* D) (trans A'≡B' (sym (subset* D')))

reductionₜ : ∀ {a a' b b' A B Γ}
           → Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a' ∷ B
           → Γ ⊢ b ⇒* b' ∷ B
           → Whnf B
           → Whnf a'
           → Whnf b'
           → Γ ⊢ a' ≡ b' ∷ B
           → Γ ⊢ a ≡ b ∷ A
reductionₜ D d d' whnfB whnfA' whnfB' a'≡b' =
  conv (trans (subset*Term d)
              (trans a'≡b' (sym (subset*Term d'))))
       (sym (subset* D))

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
