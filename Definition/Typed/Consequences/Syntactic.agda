{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Syntactic where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Escape
open import Definition.LogicalRelation.Fundamental
open import Definition.Typed.Consequences.Injectivity

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Syntactic validity of type equality.
syntacticEq : ∀ {A B} → Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
syntacticEq A≡B with fundamentalEq A≡B
syntacticEq A≡B | [Γ] , [A] , [B] , [A≡B] =
  escapeᵛ [Γ] [A] , escapeᵛ [Γ] [B]

-- Syntactic validity of terms.
syntacticTerm : ∀ {t A} → Γ ⊢ t ∷ A → Γ ⊢ A
syntacticTerm t with fundamentalTerm t
syntacticTerm t | [Γ] , [A] , [t] = escapeᵛ [Γ] [A]

-- Syntactic validity of term equality.
syntacticEqTerm : ∀ {t u A} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ A × (Γ ⊢ t ∷ A × Γ ⊢ u ∷ A)
syntacticEqTerm t≡u with fundamentalTermEq t≡u
syntacticEqTerm t≡u | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  escapeᵛ [Γ] [A] , escapeTermᵛ [Γ] [A] [t] , escapeTermᵛ [Γ] [A] [u]

-- Syntactic validity of type reductions.
syntacticRed : ∀ {A B} → Γ ⊢ A ⇒* B → Γ ⊢ A × Γ ⊢ B
syntacticRed D = syntacticEq (subset* D)

-- Syntactic validity of term reductions.
syntacticRedTerm : ∀ {t u A} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A × (Γ ⊢ t ∷ A × Γ ⊢ u ∷ A)
syntacticRedTerm d = syntacticEqTerm (subset*Term d)

-- Syntactic validity of Π-types.
syntacticΠ : ∀ {F G} → Γ ⊢ Π F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΠ ΠFG with injectivity (refl ΠFG)
syntacticΠ ΠFG | F≡F , G≡G = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)

syntacticΣ : ∀ {F G} → Γ ⊢ Σ F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΣ ΣFG with Σ-injectivity (refl ΣFG)
syntacticΣ ΣFG | F≡F , G≡G = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)
