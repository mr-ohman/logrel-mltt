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

canonicity''' : ∀ {t}
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity''' (suc (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity''' prop
  in  suc a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity''' zero = zero , refl (zero ε)
canonicity''' (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noNe ⊢k neK)

canonicity'' : ∀ {t l}
             → ([ℕ] : _⊩⟨_⟩ℕ_ {{eqRelInstance}} ε l ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity'' (noemb [ℕ]) (ℕₜ n d n≡n prop) =
  let a , b = canonicity''' prop
  in  a , trans (subset*Term (redₜ d)) b
canonicity'' (emb 0<1 [ℕ]) [t] = canonicity'' [ℕ] [t]

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
