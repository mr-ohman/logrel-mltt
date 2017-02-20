module Definition.Typed.Consequences.Canonicity where

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties

open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps

open import Definition.Typed.EqRelInstance

open import Definition.LogicalRelation
import Definition.LogicalRelation.Weakening as LR
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Fundamental

open import Tools.Empty
open import Tools.Unit
open import Tools.Nat
open import Tools.Product

import Tools.PropositionalEquality as PE


sucᵏ : Nat → Term
sucᵏ zero = zero
sucᵏ (suc n) = suc (sucᵏ n)

canonicity'' : ∀ {t l}
             → ([ℕ] : _⊩⟨_⟩ℕ_ {{eqRelInstance}} ε l ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity'' {l = l} (noemb D) (ℕₜ _ d _ suc prop) =
  let a , b = canonicity'' {l = l} (noemb D) prop
  in  suc a , trans (subset*Term (redₜ d)) (suc-cong b)
canonicity'' (noemb D) (ℕₜ .zero d _ zero prop) = zero , subset*Term (redₜ d)
canonicity'' (noemb D) (ℕₜ n d _ (ne x) (neNfₜ _ prop _)) = ⊥-elim (noNe prop x)
canonicity'' (emb 0<1 x) [t] = canonicity'' x [t]

canonicity' : ∀ {t l}
            → ([ℕ] : ε ⊩⟨ l ⟩ ℕ)
            → ε ⊩⟨ l ⟩ t ∷ ℕ / [ℕ]
            → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity' [ℕ] [t] =
  canonicity'' (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

canonicity : ∀ {t} → ε ⊢ t ∷ ℕ → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity ⊢t with fundamentalTerm ⊢t
canonicity ⊢t | ε , [ℕ] , [t] =
  let [ℕ]' = proj₁ ([ℕ] {σ = idSubst} ε tt)
      [t]' = irrelevanceTerm'' PE.refl (substIdEq _) [ℕ]' [ℕ]' (proj₁ ([t] ε tt))
  in  canonicity' [ℕ]' [t]'
