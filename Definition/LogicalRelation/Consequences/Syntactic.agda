module Definition.LogicalRelation.Consequences.Syntactic where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Wellformed
open import Definition.LogicalRelation.Fundamental
open import Definition.LogicalRelation.Consequences.Injectivity

open import Tools.Product


syntacticEq : ∀ {A B Γ} → Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
syntacticEq A≡B with fundamentalEq A≡B
syntacticEq A≡B | [Γ] , [A] , [B] , [A≡B] =
  wellformedₛ [Γ] [A] , wellformedₛ [Γ] [B]

syntacticTerm : ∀ {t A Γ} → Γ ⊢ t ∷ A → Γ ⊢ A
syntacticTerm t with fundamentalTerm t
syntacticTerm t | [Γ] , [A] , [t] = wellformedₛ [Γ] [A]

syntacticEqTerm : ∀ {t u A Γ} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ A × (Γ ⊢ t ∷ A × Γ ⊢ u ∷ A)
syntacticEqTerm t≡u with fundamentalTermEq t≡u
syntacticEqTerm t≡u | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  wellformedₛ [Γ] [A] , wellformedTermₛ [Γ] [A] [t] , wellformedTermₛ [Γ] [A] [u]

syntacticΠ : ∀ {Γ F G} → Γ ⊢ Π F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΠ ΠFG with injectivity (refl ΠFG)
syntacticΠ ΠFG | F≡F , G≡G = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)
