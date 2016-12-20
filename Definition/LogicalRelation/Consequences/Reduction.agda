module Definition.LogicalRelation.Consequences.Reduction where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
import Tools.PropositionalEquality as PE


fullyReducible' : ∀ {a A Γ l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a ⇒* b ∷ A
fullyReducible' (U x) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , redₜ d
fullyReducible' (ℕ x) (ℕₜ n d n≡n natN prop) =
  n , naturalWhnf natN , conv* (redₜ d) (sym (subset* (red x)))
fullyReducible' (ne x) (neₜ k d (neNfₜ neK ⊢k k≡k)) = k , ne neK , redₜ d
fullyReducible' (Π x) (Πₜ f d funcF f≡f [f] [f]₁) = f , functionWhnf funcF , redₜ d
fullyReducible' (emb 0<1 [A]) [a] = fullyReducible' [A] [a]

fullyReducible : ∀ {a A Γ} → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a ⇒* b ∷ A
fullyReducible a with fundamentalTerm a
... | [Γ] , [A] , [a] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
      b , whnfB , d = fullyReducible' (proj₁ ([A] ⊢Γ [id])) (proj₁ ([a] ⊢Γ [id]))
  in  b , whnfB
  ,   PE.subst₂ (λ x y → _ ⊢ x ⇒* b ∷ y) (substIdEq _) (substIdEq _) d
