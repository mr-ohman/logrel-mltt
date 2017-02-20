module Definition.Conversion.Consequences.Validity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Conversion

open import Definition.Conversion.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Wellformed
open import Definition.LogicalRelation.Fundamental

open import Tools.Product


validEq : ∀ {A B Γ} → Γ ⊢ A ≡ B → Γ ⊢ A [conv↑] B
validEq A≡B =
  let [Γ] , [A] , [B] , [A≡B] = fundamentalEq A≡B
  in  wellformedEqₛ [Γ] [A] [A≡B]

validEqTerm : ∀ {t u A Γ} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t [conv↑] u ∷ A
validEqTerm t≡u =
  let [Γ] , modelsTermEq [A] [t] [u] [t≡u] = fundamentalTermEq t≡u
  in  wellformedEqTermₛ [Γ] [A] [t≡u]
