{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Consequences.Completeness where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Conversion

open import Definition.Conversion.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Escape
open import Definition.LogicalRelation.Fundamental

open import Tools.Product


-- Algorithmic equality is derivable from judgemental equality of types.
completeEq : ∀ {A B Γ} → Γ ⊢ A ≡ B → Γ ⊢ A [conv↑] B
completeEq A≡B =
  let [Γ] , [A] , [B] , [A≡B] = fundamentalEq A≡B
  in  escapeEqᵛ [Γ] [A] [A≡B]

-- Algorithmic equality is derivable from judgemental equality of terms.
completeEqTerm : ∀ {t u A Γ} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t [conv↑] u ∷ A
completeEqTerm t≡u =
  let [Γ] , modelsTermEq [A] [t] [u] [t≡u] = fundamentalTermEq t≡u
  in  escapeEqTermᵛ [Γ] [A] [t≡u]
