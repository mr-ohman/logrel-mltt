{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Tools.Nat

private
  variable
    n : Nat
    Γ : Con Term n
    A A′ B B′ : Term n
    a a′ b b′ : Term n

-- Weak head expansion of type equality
reduction : Γ ⊢ A ⇒* A′
          → Γ ⊢ B ⇒* B′
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≡ B′
          → Γ ⊢ A ≡ B
reduction D D′ whnfA′ whnfB′ A′≡B′ =
  trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

reduction′ : Γ ⊢ A ⇒* A′
           → Γ ⊢ B ⇒* B′
           → Whnf A′
           → Whnf B′
           → Γ ⊢ A ≡ B
           → Γ ⊢ A′ ≡ B′
reduction′ D D′ whnfA′ whnfB′ A≡B =
  trans (sym (subset* D)) (trans A≡B (subset* D′))

-- Weak head expansion of term equality
reductionₜ : Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a′ ∷ B
           → Γ ⊢ b ⇒* b′ ∷ B
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≡ b′ ∷ B
           → Γ ⊢ a ≡ b ∷ A
reductionₜ D d d′ whnfB whnfA′ whnfB′ a′≡b′ =
  conv (trans (subset*Term d)
              (trans a′≡b′ (sym (subset*Term d′))))
       (sym (subset* D))

reductionₜ′ : Γ ⊢ A ⇒* B
            → Γ ⊢ a ⇒* a′ ∷ B
            → Γ ⊢ b ⇒* b′ ∷ B
            → Whnf B
            → Whnf a′
            → Whnf b′
            → Γ ⊢ a ≡ b ∷ A
            → Γ ⊢ a′ ≡ b′ ∷ B
reductionₜ′ D d d′ whnfB whnfA′ whnfB′ a≡b =
  trans (sym (subset*Term d))
        (trans (conv a≡b (subset* D)) (subset*Term d′))
