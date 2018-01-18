{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.SucCong where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Nat
open import Tools.Product


-- Congurence of the type of the successor case in natrec.
sucCong : ∀ {F G Γ} → Γ ∙ ℕ ⊢ F ≡ G
        → Γ ⊢ Π ℕ ▹ (F ▹▹ F [ suc (var 0) ]↑)
            ≡ Π ℕ ▹ (G ▹▹ G [ suc (var 0) ]↑)
sucCong F≡G with wfEq F≡G
sucCong F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , _ = syntacticEq F≡G
  in  Π-cong ⊢ℕ (refl ⊢ℕ)
             (Π-cong ⊢F F≡G
                     (wkEq (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢F)
                           (subst↑TypeEq F≡G
                                         (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ) here))))))
