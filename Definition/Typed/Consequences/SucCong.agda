{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.SucCong where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Fin
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Congruence of the type of the successor case in natrec.
sucCong : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
        → Γ ⊢ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
            ≡ Π ℕ ▹ (G ▹▹ G [ suc (var x0) ]↑)
sucCong F≡G with wfEq F≡G
sucCong F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , _ = syntacticEq F≡G
  in  Π-cong ⊢ℕ (refl ⊢ℕ)
             (Π-cong ⊢F F≡G
                     (wkEq (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢F)
                           (subst↑TypeEq F≡G
                                         (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ) here))))))
